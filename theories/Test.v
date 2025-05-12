From Coq Require Import Lia String.
From Ltac2 Require Ltac2.
From Ltac2 Require Import Printf.
From Prototype Require Import Prelude Sig.
From Prototype Require Constants LevelOne LevelTwo LevelTwoIrred LevelTwoSimp.

Declare ML Module "autosubst-experiments.plugin".
Ltac2 @external reify : constr -> constr * constr := "autosubst-experiments.plugin" "reify".

Autosubst Generate.

Class TermSimplification (t s : term) := 
  MkTermSimplification { term_simplification : t = s }.

Arguments term_simplification t {s _}.
Hint Mode TermSimplification + - : typeclass_instances.

Lemma autosubst_simpl_term_substitute s t res :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl.

Lemma congr_eval : 
  forall k (t1 t2 : T.O.expr k), t1 = t2 -> eval k t1 = eval k t2.
Proof. now intros k t1 t2 ->. Qed.

From Ltac2 Require Import RedFlags.

Ltac2 rasimpl_red_flags () : RedFlags.t := 
  red_flags:(beta delta [T.eeval]).


(** Solve a goal of the form [TermSimplification t0]. *)
Ltac2 build_TermSimplification (t0 : constr) : unit :=
  (* Reify Level 0 -> Level 1. *)
  let (t1, p1) := reify t0 in 
  let p1 := constr:(eq_sym $p1) in
  printf "t1 := %t" t1;
  printf "p1 := %t" (Constr.type p1);
  (* Reify Level 1 -> Level 2. *)
  let env := T.empty_env () in
  let (env, t2) := T.reify_expr env t1 in
  let env := T.build_env env in
  printf "t2 := %t" t2;
  (* Simplify. *)
  let t2' := constr:(T.esimp $t2) in
  let p2 := constr:(eq_sym (T.esimp_sound $env $t2)) in
  printf "t2' := %t" t2';
  printf "p2 := %t" p2;
  let t2'' := Std.eval_cbn rasimpl_red_flags t2 in 
  (* Build the instance of [TermSimplification t0]. *)
  let t0' := constr:(eval Kt (T.eeval $env $t2')) in
  let eq := constr:(eq_trans $p1 (congr_eval Kt $t1 _ $p2)) in
  printf "t0' := %t" t0';
  exact (MkTermSimplification $t0 $t0' $eq).
  
#[export] Hint Extern 10 (TermSimplification ?t0 _) =>
  let tac := ltac2:(t0 |-  
    match Ltac1.to_constr t0 with 
    | Some t0 => build_TermSimplification t0
    | None => Control.throw_invalid_argument "build_TermSimplification"
    end) 
  in 
  tac t0 : typeclass_instances.
    
Ltac rasimpl := (rewrite_strat (topdown (hints asimpl))) ; [ | (exact _) ..].

Lemma test : substitute sid (substitute (scomp sshift sid) (Var 0)) = Var 0.
Proof. rasimpl.

Qed.



(*Autosubst Reify (substitute (scomp sid (scons (Var 0) sid)) (Var 0)).*)
(*Autosubst Reify (rename (rcomp rid rshift) (Var 0)).*)
(*Autosubst Reify (Lam "x" (Var 0)).*)
(*Autosubst Eval (T.O.E_var 0).*)
