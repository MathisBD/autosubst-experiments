From Prototype Require Import Prelude Sig Constants.
From Prototype Require LevelOne LevelTwo LevelTwoClean LevelTwoSimp.
From Ltac2 Require Import RedFlags Printf.

Module O := LevelOne.
Module T := LevelTwo.
Module Simp := LevelTwoSimp.
Module Clean := LevelTwoClean.

(*********************************************************************************)
(** *** Load the plugin. *)
(*********************************************************************************)

Declare ML Module "autosubst-experiments.plugin".

Autosubst Generate {{
  
  term : Type
  
  lam : {{ nat }} -> ty -> (bind term in term) -> term
  app : {{ nat * nat }} -> term -> term -> term
  base : ty
  weird : (bind ty term in ty) -> term
}}.

Ltac2 @external reify_term : constr -> constr * constr := "autosubst-experiments.plugin" "reify_term".
Ltac2 @external reify_subst : constr -> constr * constr := "autosubst-experiments.plugin" "reify_subst".
Ltac2 @external eval_term : constr -> constr * constr := "autosubst-experiments.plugin" "eval_term".
Ltac2 @external eval_subst : constr -> constr * constr := "autosubst-experiments.plugin" "eval_subst".

(*********************************************************************************)
(** *** Reduction flags. *)
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
