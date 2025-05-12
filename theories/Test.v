From Coq Require Import Lia String.
From Ltac2 Require Ltac2.
From Ltac2 Require Import Printf RedFlags.
From Prototype Require Import Prelude Sig.
From Prototype Require Constants LevelOne LevelTwo LevelTwoIrred LevelTwoSimp.

Declare ML Module "autosubst-experiments.plugin".
Ltac2 @external reify_term : constr -> constr * constr := "autosubst-experiments.plugin" "reify_term".
Ltac2 @external eval_term : constr -> constr * constr := "autosubst-experiments.plugin" "eval_term".

Class TermSimplification {term} (t s : term) := 
  MkTermSimplification { term_simplification : t = s }.
Hint Mode TermSimplification + + - : typeclass_instances.

Autosubst Generate.

Lemma autosubst_simpl_term_substitute (s : subst) (t res : term) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl.

Ltac2 red_flags_simp () : RedFlags.t := 
  red_flags:(beta iota delta 
    [T.esimp T.ssimp T.esimp_functional T.ssimp_functional
     T.qsimp T.rsimp T.qsimp_functional T.rsimp_functional
     T.substitute T.scomp T.substitute_functional T.scomp_functional
     T.rename T.srcomp T.rename_functional T.srcomp_functional
     T.substitute_aux T.scomp_aux T.rename_aux T.sapply_aux T.rup T.sren
     T.sapply T.rscomp T.sapply_functional T.rscomp_functional
     T.rapply T.rcomp T.rapply_functional T.rcomp_functional
     T.rcomp_aux T.rapply_aux]).

Ltac2 red_flags_eval () : RedFlags.t :=
  red_flags:(beta iota delta   
    [T.eeval T.seval T.eeval_functional T.seval_functional
     T.reval T.qeval T.reval_functional T.qeval_functional
     T.assign_qnat T.assign_ren T.assign_term T.assign_subst
     List.nth (* TODO use something else than [List.nth]. *)
     ]).

(** Solve a goal of the form [TermSimplification t0]. *)
Ltac2 build_TermSimplification (t0 : constr) : unit :=
  (* Reify Level 0 -> Level 1. *)
  let (t1, p1) := reify_term t0 in 
  (* Reify Level 1 -> Level 2. *)
  let env := T.empty_env () in
  let (env, t2) := T.reify_expr env t1 in
  let env := T.build_env env in
  (* Simplify on Level 2. *)
  let t2' := Std.eval_cbv (red_flags_simp ()) constr:(T.esimp $t2) in
  (* Eval Level 2 -> Level 1. *)
  let t1' := Std.eval_cbv (red_flags_eval ()) constr:(T.eeval $env $t2') in
  (* Eval Level 1 -> Level 0. *)
  let (t0', p3) := eval_term t1' in
  (* Assemble the typeclass instance. *)
  let eq := constr:(eq_trans
    (eq_sym $p1) 
    (eq_trans 
      (f_equal (eval Kt) (eq_sym (T.esimp_sound $env $t2))) 
      $p3)) 
  in
  exact (MkTermSimplification term $t0 $t0' $eq).

#[export] Hint Extern 10 (TermSimplification ?t0 _) =>
  let tac := ltac2:(t0 |-  
    match Ltac1.to_constr t0 with 
    | Some t0 => build_TermSimplification t0
    | None => Control.throw_invalid_argument "build_TermSimplification"
    end) 
  in 
  tac t0 : typeclass_instances.
    
Ltac rasimpl := (rewrite_strat (topdown (hints asimpl))) ; [ | (exact _) ..].

Axiom (t : term).
Axiom (s : subst).
Lemma test : substitute (scons t s) (Var 1) = Var 0.
Proof. rasimpl.
    About seval_sreify_inv.

Admitted.

(*Autosubst Reify (substitute (scomp sid (scons (Var 0) sid)) (Var 0)).*)
(*Autosubst Reify (rename (rcomp rid rshift) (Var 0)).*)
(*Autosubst Reify (Lam "x" (Var 0)).*)
(*Autosubst Eval (T.O.E_var 0).*)
