From Prototype Require Import Prelude.

(** This file defines the notion of abstract signature of a language. *)

(** Argument types over a set of base types. *)
Inductive arg_ty {base} :=
| AT_base : base -> arg_ty
| AT_term : arg_ty
| AT_bind : arg_ty -> arg_ty.

(** Kind of an expression (this is used in both level one and level two). *)
Inductive kind {base} := 
| (** Term. *)
  Kt : kind
| (** Constructor argument. *)
  Ka : @arg_ty base -> kind
| (** List of constructor arguments. *)
  Kal : list (@arg_ty base) -> kind.
Derive NoConfusion for kind.

(** Signatures for abstract terms. *)
Record signature :=
{ (** The set of base types, 
      e.g. [Inductive base := BUnit | BBool | BNat]. *)
  base : Type 
; (** The actual type that each base type represents,
      e.g. a mapping BNat => nat ; BBool => bool ; BUnit => unit. *)
  denote_base : base -> Type
;  (** The set of _non variable_ constructors, 
       e.g. [Inductive ctor := CApp | CLam]. *)
  ctor : Type
; (** The number and types of the arguments of each constructor. *)
  ctor_type : ctor -> list (@arg_ty base) }.

Module Type Sig.
  Parameter t : signature.
End Sig.
    
