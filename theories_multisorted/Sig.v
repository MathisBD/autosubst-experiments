From Prototype Require Import Prelude.

(** This file defines the notion of abstract signature of a language. *)

(** Argument types over a set of base types and a set of sorts. *)
Inductive arg_ty {base sort} :=
| AT_base : base -> arg_ty
| AT_term : sort -> arg_ty
| AT_bind : sort -> arg_ty -> arg_ty.
Derive NoConfusion NoConfusionHom for arg_ty.

(** Kind of an expression (this is used in both level one and level two). *)
Inductive kind {base sort} := 
| (** Term. *)
  Kt : sort -> kind
| (** Constructor argument. *)
  Ka : @arg_ty base sort -> kind
| (** List of constructor arguments. *)
  Kal : list (@arg_ty base sort) -> kind.
Derive NoConfusion NoConfusionHom for kind.

(** Signatures for abstract terms. *)
Record signature :=
{ (** The set of base types, 
      e.g. [Inductive base := BUnit | BBool | BNat]. *)
  base : Type 
; (** Decidable equality on [base]. *)
  base_EqDec : EqDec base
; (** The actual type that each base type represents,
      e.g. a mapping BNat => nat ; BBool => bool ; BUnit => unit. *)
  base_type : base -> Type
; (** The set of term sorts,  
      e.g. [Inductive sort := STy | STerm]. *)
  sort : Type 
; (** Decidable equality on [sort]. *)
  sort_EqDec : EqDec sort 
; (** Which sorts have variable constructors? *)
  sort_has_var : sort -> Prop 
; (** The set of _non variable_ constructors, 
      e.g. [Inductive ctor := CApp | CLam]. *)
  ctor : sort -> Type
; (** Decidable equality on [ctor]. *)
  ctor_EqDec : forall s, EqDec (ctor s)
; (** The number and types of the arguments of each constructor. *)
  ctor_type : forall s, ctor s -> list (@arg_ty base sort) }.

(** Most of the time we can omit writing the precise signature,
    it will be inferred by typeclass resolution. *)
Existing Class signature.

(** Set the [signature] argument of the projections to be implicit. *)
Arguments base {_}.
Arguments base_EqDec {_}.
Arguments base_type {_}.
Arguments sort {_}.
Arguments sort_EqDec {_}.
Arguments sort_has_var {_}.
Arguments ctor {_}.
Arguments ctor_EqDec {_}.
Arguments ctor_type {_}.

