From Prototype Require Import Prelude Sig Constants.
From Prototype Require LevelOne LevelTwo LevelTwoClean LevelTwoSimp.
From Ltac2 Require Import RedFlags Printf.

Module O := LevelOne.
Module T := LevelTwo.
Module Simp := LevelTwoSimp.
Module Clean := LevelTwoClean.

(*********************************************************************************)
(** *** Simplifying level one terms/substitutions. *)
(*********************************************************************************)

(** Reduction flags to unfold all (level 2 -> level 1) evaluation 
    functions (LevelTwo.v). *)
Ltac2 red_flags_eval () : RedFlags.t :=
  red_flags:(beta iota delta   
    [T.eeval T.seval T.eeval_functional T.seval_functional
     T.reval T.qeval T.reval_functional T.qeval_functional
     T.assign_qnat T.assign_ren T.assign_term T.assign_subst
     T.list_nth
     ]).
   
(** Simplify a level one term. Returns [(t1', eq)] where [eq : t1 = t1'].  *)
Ltac2 simpl_term_one (sig : constr) (t1 : constr) : constr * constr :=
  (* Reify Level 1 -> Level 2. *)
  let env := T.empty_env () in
  let (env, t2) := T.reify_expr sig env t1 in
  let env := T.build_env sig env in
  (* Simplify on Level 2. *)
  let t2' := Std.eval_cbn RedFlags.all constr:(Simp.esimp $t2) in
  let t2'' := Std.eval_cbn RedFlags.all constr:(Clean.eclean $t2') in
  (* Eval Level 2 -> Level 1. *)
  let t1' := Std.eval_cbn (red_flags_eval ()) constr:(T.eeval $env $t2'') in
  (* [eq1 : t1 = t1']. *)
  let eq1 := constr:(transitivity
    (Simp.ered_sound $env _ _ (Simp.esimp_red $t2))
    (Clean.ered_sound $env _ _ (Clean.eclean_red $t2'))) 
  in
  (t1', eq1).
  
(** Simplify a level one substitution. Returns [(s1', eq)] where [eq : s1 =₁ s1'].*)
Ltac2 simpl_subst_one (sig : constr) (s1 : constr) : constr * constr :=
  (* Reify Level 1 -> Level 2. *)
  let env := T.empty_env () in
  let (env, s2) := T.reify_subst sig env s1 in
  let env := T.build_env sig env in
  (* Simplify on Level 2. *)
  let s2' := Std.eval_cbn RedFlags.all constr:(Simp.ssimp $s2) in
  let s2'' := Std.eval_cbn RedFlags.all constr:(Clean.sclean $s2') in
  (* Eval Level 2 -> Level 1. *)
  let s1' := Std.eval_cbv (red_flags_eval ()) constr:(T.seval $env $s2'') in
  (* [eq1 : s1 =₁ s1']. *)
  let eq1 := constr:(transitivity
    (Simp.sred_sound $env _ _ (Simp.ssimp_red $s2))
    (Clean.sred_sound $env _ _ (Clean.sclean_red $s2'))) 
  in
  (s1', eq1).

(*********************************************************************************)
(** *** Load the plugin. *)
(*********************************************************************************)

Declare ML Module "autosubst-experiments.plugin".

Ltac2 @external reify_term : constr -> constr * constr := "autosubst-experiments.plugin" "reify_term".
Ltac2 @external reify_subst : constr -> constr * constr := "autosubst-experiments.plugin" "reify_subst".
Ltac2 @external eval_term : constr -> constr * constr := "autosubst-experiments.plugin" "eval_term".
Ltac2 @external eval_subst : constr -> constr * constr := "autosubst-experiments.plugin" "eval_subst".

Module Test. 

Autosubst Generate 
{{
  term : Type
  app : {{nat}} -> term -> term -> term
}}.


(*********************************************************************************)
(** *** [rasimpl]. *)
(*********************************************************************************)

(** [Simplification x y] expresses the fact that [x] simplifies into [y].
    Typically [x] is a ground term and [y] is an evar, and a proof of 
    [Simplification x y] instantiates [y] with a simplified version of [x]. *)

Class NatSimplification (x y : nat) :=
  MkNatSimplification { nat_simplification : x = y }.

Class RenSimplification (x y : nat -> nat) :=
  MkRenSimplification { ren_simplification : x =₁ y }.

Class TermSimplification {T} (x y : T) := 
  MkTermSimplification { term_simplification : x = y }.

Class SubstSimplification {T} (x y : nat -> T) :=
  MkSubstSimplification { subst_simplification : x =₁ y }.
