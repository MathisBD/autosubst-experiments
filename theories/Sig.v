From Sulfur Require Import Prelude.

(** This file defines the notion of abstract signature of a language. *)

(** Argument types over a set of base types and a set of functors. *)
Inductive arg_ty {base fctor} :=
| AT_base : base -> arg_ty
| AT_term : arg_ty
| AT_bind : arg_ty -> arg_ty
| AT_functor : fctor -> arg_ty -> arg_ty.

Derive NoConfusion NoConfusionHom for arg_ty.

(** Kind of an expression (this is used in both parameterized syntax and 
    explicit syntax). *)
Inductive kind {base fctor} := 
| (** Term. *)
  Kt : kind
| (** Constructor argument. *)
  Ka : @arg_ty base fctor -> kind
| (** List of constructor arguments. *)
  Kal : list (@arg_ty base fctor) -> kind.

Derive NoConfusion NoConfusionHom for kind.

(** Signatures for abstract grammars. *)
Record signature :=
{ (** The set of base types, 
      e.g. [Inductive base := BUnit | BBool | BNat]. *)
  base : Type 
; (** Decidable equality on [base]. *)
  base_EqDec : EqDec base
; (** The actual type that each base type represents,
      e.g. a mapping BNat => nat ; BBool => bool ; BUnit => unit. *)
  eval_base : base -> Type

; (** The set of _normal_ functors,
      e.g. [Inductive fctor := FOption | FList]. *)
  fctor : Type 
; (** Decidable equality on [fctor]. *)
  fctor_EqDec : EqDec fctor
; (** Each normal functor must have a shape. *)
  fctor_shape : fctor -> Type 
; (** Each normal functor must have a size. *)
  fctor_size : forall f, fctor_shape f -> nat

; (** The set of _non variable_ constructors, 
      e.g. [Inductive ctor := CApp | CLam]. *)
  ctor : Type
; (** Decidable equality on [ctor]. *)
  ctor_EqDec : EqDec ctor
; (** The number and types of the arguments of each constructor. *)
  ctor_type : ctor -> list (@arg_ty base fctor) }.

Arguments base {s}.
Arguments base_EqDec {s}.
Arguments eval_base {s}.
Arguments fctor {s}.
Arguments fctor_EqDec {s}.
Arguments fctor_shape {s}.
Arguments fctor_size {s}.
Arguments ctor {s}.
Arguments ctor_EqDec {s}.
Arguments ctor_type {s}.

Existing Class signature.