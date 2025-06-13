(** This file defines the notion of abstract signature of a language. *)

From MPrototype Require Import Prelude.

(*********************************************************************************)
(** *** Signatures. *)
(*********************************************************************************)

(** Argument types over a set of base types and a set of sorts. *)
Inductive arg_ty {nbase nsort} :=
| AT_base : fin nbase -> arg_ty
| AT_term : fin nsort -> arg_ty
| AT_bind : fin nsort -> arg_ty -> arg_ty.

Derive NoConfusion NoConfusionHom for arg_ty.

(** Decidable equality on argument types, to avoid UIP. *)
#[export] Instance arg_ty_EqDec nbase nsort : EqDec (@arg_ty nbase nsort).
Proof. Admitted.

(** Signatures for abstract terms. *)
Record signature :=
{ (** The number of base types. *)
  nbase : nat
; (** The actual type that each base type represents,
      e.g. a mapping BNat => nat ; BBool => bool ; BUnit => unit. *)
  base_type : fin nbase -> Type
; (** The number of sorts. *)
  nsort : nat
; (** The number of _non variable_ constructors of a given sort. *)
  nctor : fin nsort -> nat
; (** The number and types of the arguments of each constructor. *)
  ctor_type : forall (s : fin nsort) (c : fin (nctor s)), list (@arg_ty nbase nsort) }.

(** Most of the time we can omit writing the precise signature,
    it will be inferred by typeclass resolution. *)
Existing Class signature.

(** Set the [signature] argument of the projections to be implicit. *)
Arguments nbase {_}.
Arguments base_type {_}.
Arguments nsort {_}.
Arguments nctor {_}.
Arguments ctor_type {_ _}.

(** Kind of an expression (this is used in both level one and level two). *)
Inductive kind {nbase nsort} := 
| (** Term of a given sort. *)
  Kt : fin nsort -> kind
| (** Constructor argument. *)
  Ka : @arg_ty nbase nsort -> kind
| (** List of constructor arguments. *)
  Kal : list (@arg_ty nbase nsort) -> kind.

Derive NoConfusion NoConfusionHom for kind.
