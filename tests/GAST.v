From Coq Require Import Lia String.
From Ltac2 Require Import RedFlags Printf.
From Prototype Require Export Prelude.
From Prototype Require Import Sig Constants LevelOne LevelTwo LevelTwoIrred 
  LevelTwoSimp LevelTwoClean RASimpl.
From GhostTT Require Import BasicAST. 

(*********************************************************************************)
(** *** Generate all operations and lemmas. *)
(*********************************************************************************)

Register level as ghost_reflection.level.
Register mode as ghost_reflection.mode.

Time Autosubst Generate.

(*********************************************************************************)
(** *** Glue code (eventually should be generic). *)
(*********************************************************************************)

(** Solve a goal of the form [Simplification term t0 _]. *)
Ltac2 solve_term_simplification () : unit :=
  lazy_match! Control.goal () with 
  | Simplification term ?t0 _ =>
    (* Reify Level 0 -> Level 1. *)
    let (t1, p1) := reify_term t0 in 
    (* Reify Level 1 -> Level 2. *)
    let env := T.empty_env () in
    let (env, t2) := T.reify_expr env t1 in
    let env := T.build_env env in
    (* Simplify on Level 2. *)
    let t2' := Std.eval_cbv (T.red_flags_simp ()) constr:(T.esimp $t2) in
    let t2'' := Std.eval_cbv (T.red_flags_clean ()) constr:(T.eclean $t2') in
    (* Eval Level 2 -> Level 1. *)
    let t1' := Std.eval_cbv (T.red_flags_eval ()) constr:(T.eeval $env $t2'') in
    (* Eval Level 1 -> Level 0. *)
    let (t0', p3) := eval_term t1' in
    (* [eq1 : t1 = t1']. *)
    let eq1 := constr:(eq_trans 
      (eq_sym (T.esimp_sound $env $t2))
      (eq_sym (T.eclean_sound $env $t2'))) 
    in
    (* [eq0 : t0 = t0']. *)
    let eq := constr:(eq_trans
      (eq_sym $p1) 
      (eq_trans (f_equal (eval Kt) $eq1) $p3)) 
    in
    exact (MkSimplification term $t0 $t0' $eq)
  | _ => Control.zero (Tactic_failure None)
  end.

Lemma congr_seval {s1 s2} : 
  s1 =₁ s2 -> seval s1 =₁ seval s2.
Proof. intros H i. unfold seval. now rewrite H. Qed. 

(** Solve a goal of the form [Simplification subst s0 _]. *)
Ltac2 solve_subst_simplification () : unit :=
  lazy_match! Control.goal () with 
  | Simplification subst ?s0 _ =>
    (* Reify Level 0 -> Level 1. *)
    let (s1, p1) := reify_subst s0 in 
    (* Reify Level 1 -> Level 2. *)
    let env := T.empty_env () in
    let (env, s2) := T.reify_subst env s1 in
    let env := T.build_env env in
    (* Simplify on Level 2. *)
    let s2' := Std.eval_cbv (T.red_flags_simp ()) constr:(T.ssimp $s2) in
    let s2'' := Std.eval_cbv (T.red_flags_clean ()) constr:(T.sclean $s2') in
    (* Eval Level 2 -> Level 1. *)
    let s1' := Std.eval_cbv (T.red_flags_eval ()) constr:(T.seval $env $s2'') in
    (* Eval Level 1 -> Level 0. *)
    let (s0', p3) := eval_subst s1' in
    (* [eq1 : s1 =₁ s1']. *)
    let eq1 := constr:(transitivity
      (symmetry (T.ssimp_sound $env $s2))
      (symmetry (T.sclean_sound $env $s2'))) 
    in
    (* [eq0 : s0 =₁ s0']. *)
    let eq := constr:(transitivity
      (symmetry $p1) 
      (transitivity (congr_seval $eq1) $p3)) 
    in
    exact (MkSimplification subst $s0 $s0' $eq)
  | _ => Control.zero (Tactic_failure None) 
  end.

(** Main simplification tactic. *)
Ltac rasimpl := 
  (try rewrite_strat (topdown (hints asimpl))) ; 
  [ | solve [ltac2:(solve_term_simplification ()) | ltac2:(solve_subst_simplification ())] ..].

(** Trigger for [rasimpl]. *)
Lemma autosubst_simpl_term_rename (r : ren) (t res : term) :
  Simplification term (rename r t) res -> rename r t = res.
Proof. intros H. now apply simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_rename : asimpl.

(** Trigger for [rasimpl]. *)
Lemma autosubst_simpl_term_substitute (s : subst) (t res : term) :
  Simplification term (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl.

Axiom r : ren.
Axiom s : subst.
Axiom t : term.
Lemma test : rename r (lam mType (Var 0) t) = Var 0.
Proof. rasimpl. Admitted.