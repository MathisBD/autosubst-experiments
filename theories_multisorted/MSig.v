From Prototype Require Import MPrelude.

(** This file defines the notion of abstract signature of a language. *)

(** Argument types over a set of base types and a set of sorts. *)
Inductive arg_ty {nbase nsort} :=
| AT_base : fin nbase -> arg_ty
| AT_term : fin nsort -> arg_ty
| AT_bind : fin nsort -> arg_ty -> arg_ty.
Derive NoConfusion NoConfusionHom for arg_ty.

(** Kind of an expression (this is used in both level one and level two). *)
Inductive kind {nbase nsort} := 
| (** Term. *)
  Kt : fin nsort -> kind
| (** Constructor argument. *)
  Ka : @arg_ty nbase nsort -> kind.
Derive NoConfusion NoConfusionHom for kind.

(** Signatures for abstract terms. *)
Record signature :=
{ nbase : nat 
; base_type : fin nbase -> Type
; nsort : nat 
; nctor : fin nsort -> nat
; ctor_type : forall s, fin (nctor s) -> list (@arg_ty nbase nsort) }.

(** Most of the time we can omit writing the precise signature,
    it will be inferred by typeclass resolution. *)
Existing Class signature.

(** Set the [signature] argument of the projections to be implicit. *)
Arguments nbase {_}.
Arguments base_type {_}.
Arguments nsort {_}.
Arguments nctor {_}.
Arguments ctor_type {_ _}.

