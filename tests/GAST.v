From Coq Require Import Lia String.
From Ltac2 Require Import RedFlags Printf.
From Prototype Require Export Prelude.
From Prototype Require Import RASimpl.
From GhostTT Require Import BasicAST. 

Module O := LevelOne.
Module T := LevelTwo.
Module Clean := LevelTwoClean.

(*********************************************************************************)
(** *** Generate all operations and lemmas. *)
(*********************************************************************************)

Register level as ghost_reflection.level.
Register mode as ghost_reflection.mode.

Time Autosubst Generate.

(*********************************************************************************)
(** *** Glue code (eventually should be generic). *)
(*********************************************************************************)

(** Solve a goal of the form [TermSimplification t0 _]. *)
Ltac2 solve_term_simplification () : unit :=
  lazy_match! Control.goal () with 
  | TermSimplification ?t0 _ =>
    (* Reify Level 0 -> Level 1. *)
    let (t1, p1) := reify_term t0 in 
    printf "t1: %t" t1;
    (* Reify Level 1 -> Level 2. *)
    let env := T.empty_env () in
    let (env, t2) := T.reify_expr constr:(sig) env t1 in
    printf "t2: %t" t2;
    let env := T.build_env constr:(sig) env in
    (* Simplify on Level 2. *)
    let t2' := Std.eval_cbv (red_flags_simp ()) constr:(Simp.esimp $t2) in
    printf "t2': %t" t2';
    let t2'' := Std.eval_cbv (red_flags_clean ()) constr:(Clean.eclean $t2') in
    printf "t2'': %t" t2'';
    (* Eval Level 2 -> Level 1. *)
    let t1' := Std.eval_cbv (red_flags_eval ()) constr:(T.eeval $env $t2'') in
    printf "t1': %t" t1';
    (* Eval Level 1 -> Level 0. *)
    let (t0', p3) := eval_term t1' in
    printf "t0': %t" t0';
    (* [eq1 : t1 = t1']. *)
    let eq1 := constr:(eq_trans
      (Simp.ered_sound $env _ _ (Simp.esimp_red $t2))
      (Clean.ered_sound $env _ _ (Clean.eclean_red $t2'))) 
    in
    (* [eq0 : t0 = t0']. *)
    let eq := constr:(eq_trans
      (eq_sym $p1) 
      (eq_trans (f_equal (eval Sig.Kt) $eq1) $p3)) 
    in
    exact (MkTermSimplification _ $t0 $t0' $eq)
  | _ => Control.zero (Tactic_failure None)
  end.

Lemma congr_seval {s1 s2} : 
  s1 =₁ s2 -> seval s1 =₁ seval s2.
Proof. intros H i. unfold seval. now rewrite H. Qed. 

(** Solve a goal of the form [Simplification subst s0 _]. *)
Ltac2 solve_subst_simplification () : unit :=
  lazy_match! Control.goal () with 
  | SubstSimplification ?s0 _ =>
    printf "Simplifying substitution: %t" s0;
    (* Reify Level 0 -> Level 1. *)
    let (s1, p1) := reify_subst s0 in 
    (* Reify Level 1 -> Level 2. *)
    let env := T.empty_env () in
    let (env, s2) := T.reify_subst constr:(sig) env s1 in
    let env := T.build_env constr:(sig) env in
    (* Simplify on Level 2. *)
    let s2' := Std.eval_cbv (red_flags_simp ()) constr:(Simp.ssimp $s2) in
    let s2'' := Std.eval_cbv (red_flags_clean ()) constr:(Clean.sclean $s2') in
    (* Eval Level 2 -> Level 1. *)
    let s1' := Std.eval_cbv (red_flags_eval ()) constr:(T.seval $env $s2'') in
    (* Eval Level 1 -> Level 0. *)
    let (s0', p3) := eval_subst s1' in
    (* [peq1 : s1 =₁ s1']. *)
    let peq1 := constr:(transitivity
      (Simp.sred_sound $env _ _ (Simp.ssimp_red $s2))
      (Clean.sred_sound $env _ _ (Clean.sclean_red $s2'))) 
    in
    (* [peq0 : s0 =₁ s0']. *)
    let peq0 := constr:(transitivity
      (symmetry $p1) 
      (transitivity (congr_seval $peq1) $p3)) 
    in
    exact (MkSubstSimplification _ $s0 $s0' $peq0)
  | _ => Control.zero (Tactic_failure None)
  end.

(** Solve a goal of the form [Simplification _ _ _] or [PSimplification _ _ _]. *)
Ltac solve_simplification :=
  solve [ ltac2:(solve_term_simplification ()) 
        | ltac2:(solve_subst_simplification ()) ].

Ltac rasimpl_topdown := 
  (rewrite_strat (topdown (hints asimpl_topdown))) ; [| solve_simplification ..].

Ltac rasimpl_outermost := 
  (rewrite_strat (outermost (hints asimpl_outermost))) ; [| solve_simplification ..].

(** Main simplification tactic. *)
Ltac rasimpl := 
  repeat rasimpl_topdown ;
  repeat rasimpl_outermost.

(** Trigger [rasimpl] on [rename _ _]. *)
Lemma autosubst_simpl_term_rename (r : ren) (t res : term) :
  TermSimplification (rename r t) res -> rename r t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_rename : asimpl_topdown.

(** Trigger [rasimpl] on [substitute _ _]. *)
Lemma autosubst_simpl_term_substitute (s : subst) (t res : term) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl_topdown.

Axiom r : ren.
Axiom s : subst.
Axiom t : term.
Axiom i : nat.
Lemma test : substitute (scomp sshift (scons (Var 0) sid)) t = Var 0.
Proof. rasimpl_topdown. Admitted.