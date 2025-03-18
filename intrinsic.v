From Coq Require Import String List.
Import ListNotations.

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Forall combinator in Type. *)
(*Inductive All {A} (P : A -> Type) : list A -> Type :=
| All_nil : All P []
| All_cons : forall (x : A) (l : list A),
    P x -> All P l -> All P (x :: l).
Arguments All {A} P%_type _.
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.
#[global] Hint Constructors All : core.*)

(** Argument types over a set of base types. *)
Inductive arg_ty {base} :=
  | TBase : base -> arg_ty
  | TVar : arg_ty
  | TTerm : arg_ty
  | TBind : arg_ty -> arg_ty.

(** Signatures for abstract terms. *)
Module Type Signature.
  (** The set of base types, 
      e.g. [Inductive base := Unit | Bool | Nat]. *)
  Parameter base : Type.
  (** The actual type that each base type represents,
      e.g. a mapping Nat => nat ; Bool => bool ; Unit => unit. *)
  Parameter base_type : base -> Type.
  
  (** The set of constructors. *)
  Parameter ctor : Type.
  (** The number and type of each constructor argument. *)
  Parameter ctor_type : ctor -> list (@arg_ty base). 
End Signature.

Module AbstractTerms (S : Signature).
Export S.
Definition arg_ty := @arg_ty base.

(** Term grammar. Terms are well-formed by construction,
    i.e. we enforce that constructors are applied to the right number 
    and types of arguments _intrinsically_ instead of _extrinsically_. *)
Inductive term : Type :=
| Actor : forall c, arg_list (ctor_type c) -> term
(** [arg_list tys] represents a list of arguments of types [tys]. *)
with arg_list : list arg_ty -> Type :=
| ANil : arg_list []
| ACons {ty tys} : arg ty -> arg_list tys -> arg_list (ty :: tys)
(** [arg ty] represents a single argument of type [ty]. *)
with arg : arg_ty -> Type :=
| ABase : forall b, base_type b -> arg (TBase b)
| AVar : nat -> arg TVar
| ATerm : term -> arg TTerm
| ABind {ty} : arg ty -> arg (TBind ty).

(* TODO: prove a proper induction principle for terms. *)

(** Lift a renaming, e.g. when we pass through a binder. *)
Definition up_ren (f : nat -> nat) : nat -> nat :=
  fun n =>
    match n with 
    | 0 => 0
    | S n => S (f n)
    end.

(** Apply a renaming - i.e. a mapping [nat -> nat] - to a term. *)
Fixpoint ren_term (f : nat -> nat) (t : term) : term :=
  match t with 
  | Actor c args => Actor c (ren_arg_list f args)
  end
with ren_arg_list {tys} (f : nat -> nat) (args : arg_list tys) :=
  match args with 
  | ANil => ANil
  | ACons arg args => ACons (ren_arg f arg) (ren_arg_list f args)
  end
with ren_arg {ty} (f : nat -> nat) (a : arg ty) :=
  match a with 
  | ABase b x => ABase b x
  | AVar n => AVar (f n)
  | ATerm t => ATerm (ren_term f t)
  | ABind a' => ABind (ren_arg f a')
  end.

End AbstractTerms.

(** *** Example : lambda calculus. *)

(** Concrete terms. 
    Applications carry a boolean.
    Lambda abstractions contain the name of the bound variable as a string. *)
Inductive cterm :=
  | Var : nat -> cterm
  | App : bool -> cterm -> cterm -> cterm
  | Lam : string -> cterm -> cterm.

(** Abstract signature. *)

Module S.
  Inductive base_ := BString | BBool.
  Definition base := base_.
  
  Definition base_type (b : base) : Type :=
    match b with BString => string | BBool => bool end.
  
  Inductive ctor_ := CVar | CApp | CLam. 
  Definition ctor := ctor_. 

  Definition ctor_type (c : ctor) : list arg_ty :=
    match c with 
    | CVar => [ TVar ]
    | CApp => [ TBase BBool ; TTerm ; TTerm ]
    | CLam => [ TBase BString ; TBind (TTerm) ]
    end.
End S.

(** Abstract terms. *)
Module A := AbstractTerms (S).
Definition aterm := A.term.
Import A.

(** Mapping from concrete terms to abstract terms. *)
Fixpoint reify (t : cterm) : aterm :=
  match t with 
  | Var n => Actor CVar (ACons (AVar n) ANil)
  | App b t1 t2 => 
    Actor CApp 
      (ACons (ABase BBool b) 
      (ACons (ATerm (reify t1)) 
      (ACons (ATerm (reify t2))
       ANil)))
  | Lam s t => 
    Actor CLam 
      (ACons (ABase BString s) 
      (ACons (ABind (ATerm (reify t)))
       ANil))
  end.

(**************)
(** Denote argument types into [Type], 
    given a denotation [T] for the type of terms. *)
Fixpoint denote_arg_ty (T : Type) (ty : arg_ty) : Type :=
  match ty with 
  | TBase b => base_type b
  | TVar => nat
  | TTerm => T
  | TBind ty => denote_arg_ty T ty
  end.

(** Denote the type of a term constructor with arguments in [tys],
    given a denotation [T] for the type of terms. *)
Fixpoint denote_ctor_ty (T : Type) (tys : list arg_ty) : Type :=
  match tys with 
  | [] => T
  | ty :: tys => denote_arg_ty T ty -> denote_ctor_ty T tys
  end. 
(**************)

Definition denote_ctor (c : ctor) : denote_ctor_ty cterm (ctor_type c) :=
  match c with 
  | CVar => Var 
  | CApp => App
  | CLam => Lam
  end.

(** Mapping from abstract terms to concrete terms. *)
Fixpoint denote (t : aterm) : cterm :=
  match t with 
  | Actor c args => denote_args (denote_ctor c) args
  end
with denote_args {tys} (hd : denote_ctor_ty cterm tys) (args : arg_list tys) : cterm :=
  match args, hd with 
  | ANil, hd => hd
  | ACons a args, hd => denote_args (hd (denote_arg a)) args
  end
with denote_arg {ty} (a : arg ty) : denote_arg_ty cterm ty :=
  match a in arg ty0 return denote_arg_ty cterm ty0 with 
  | ABase b x => x
  | AVar n => n
  | ATerm t => denote t
  | ABind a' => denote_arg a'
  end.

  

