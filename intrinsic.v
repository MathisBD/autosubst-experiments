From Coq Require Import String List Morphisms.
Import ListNotations.

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Argument types over a set of base types. *)
Inductive arg_ty {base} :=
| AT_base : base -> arg_ty
| AT_term : arg_ty
| AT_bind : arg_ty -> arg_ty.

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

(** Terms from the sigma calculus. Terms are well-formed by construction,
    i.e. we enforce that constructors are applied to the right number 
    and types of arguments _intrinsically_ instead of _extrinsically_. *)
Inductive term : Type :=
| (* A term variable. *)
  T_var : nat -> term
| (* A term constructor, applied to a list of arguments. *)
  T_ctor : forall c, args (ctor_type c) -> term
| (* An explicit substitution, applied to a term. *)
  T_subst : term -> subst -> term
with args : list arg_ty -> Type :=
| AS_nil : args []
| AS_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)
| AS_subst {tys} : args tys -> subst -> args tys
(** [arg ty] represents a single argument of type [ty]. *)
with arg : arg_ty -> Type :=
| A_base : forall b, base_type b -> arg (AT_base b)
| A_term : term -> arg AT_term
| A_bind {ty} : arg ty -> arg (AT_bind ty)
| A_subst {ty} : arg ty -> subst -> arg ty
(** Explicit substitutions. *)
with subst : Type :=
| (* The successor subsitution: it maps [n] to [n+1]. *)
  S_succ : subst
| S_cons : term -> subst -> subst
| (* [S_comp s1 s2] applies [s2] followed by [s1]. 
     It is equivalent to [s1 ∘ s2]. *)
  S_comp : subst -> subst -> subst.

(* Custom notations to ease writing terms and substitutions. *)
Notation "t .: s" := (S_cons t s) (at level 70, right associativity).
Notation "s1 ∘ s2" := (S_comp s1 s2) (at level 50, left associativity).
Notation "t '[:' s ']'" := (T_subst t s) (at level 40, s at level 0, no associativity).
Notation "b '[,' s ']'" := (AS_subst b s) (at level 40, s at level 0, no associativity).
Notation "a '[.' s ']'" := (A_subst a s) (at level 40, s at level 0, no associativity).

(** The identity substitution. *)
Definition S_id : subst := T_var 0 .: S_succ.

Scheme term_ind' := Induction for term Sort Prop
  with args_ind' := Induction for args Sort Prop
  with arg_ind' := Induction for arg Sort Prop
  with subst_ind' := Induction for subst Sort Prop.

Reserved Notation "t1 =t= t2" (at level 75, no associativity).
Reserved Notation "as1 =al= as2" (at level 75, no associativity).
Reserved Notation "a1 =a= a2" (at level 75, no associativity).
Reserved Notation "s1 =s= s2" (at level 75, no associativity).

(** [t =t= t'] means that the terms [t] and [t'] are equal 
    modulo the equational theory of sigma calculus. *)
Inductive seq_term : term -> term -> Prop :=
(* Congruence. *)
| seq_term_var n : T_var n =t= T_var n
| seq_term_ctor c args1 args2 : 
    args1 =al= args2 -> T_ctor c args1 =t= T_ctor c args2
| seq_term_subst t1 t2 s1 s2 : 
    t1 =t= t2 -> s1 =s= s2 -> t1[: s1 ] =t= t2[: s2 ] 
(* Sigma. *)
| seq_term_zero_cons s t : (T_var 0)[: t .: s ] =t= t
| seq_term_push_subst c args s : (T_ctor c args)[: s ] =t= T_ctor c (args[, s])
with seq_args : forall tys, args tys -> args tys -> Prop :=
| seq_args_nil : AS_nil =al= AS_nil
| seq_args_cons ty tys (a1 a2 : arg ty) (b1 b2 : args tys) : 
    a1 =a= a2 -> b1 =al= b2 -> AS_cons a1 b1 =al= AS_cons a2 b2
| seq_args_subst tys (a1 a2 : args tys) s1 s2 :
    a1 =al= a2 -> s1 =s= s2 -> AS_subst a1 s1 =al= AS_subst a2 s2
| seq_args_push_subst ty tys (a : arg ty) (b : args tys) s :
    (AS_cons a b)[, s ] =al= AS_cons (a[.s]) (b[,s])
with seq_arg : forall ty, arg ty -> arg ty -> Prop :=
(* Congruence. *)
| seq_arg_congr_base b x : A_base b x =a= A_base b x 
| seq_arg_congr_term t1 t2 : t1 =t= t2 -> A_term t1 =a= A_term t2
| seq_arg_congr_bind ty (a1 a2 : arg ty) : a1 =a= a2 -> A_bind a1 =a= A_bind a2
| seq_arg_congr_subst ty (a1 a2 : arg ty) s1 s2 : 
    a1 =a= a2 -> s1 =s= s2 -> a1[. s1 ] =a= a2[. s2 ]
(* Sigma. *) 
| seq_arg_bind ty (a : arg ty) s : 
    (A_bind a)[. s ] =a= A_bind (a[. T_var 0 .: s ∘ S_succ ])
with seq_subst : subst -> subst -> Prop :=
(* Congruence. *)
| seq_subst_congr_succ : S_succ =s= S_succ
| seq_subst_congr_cons t1 t2 s1 s2 : 
    t1 =t= t2 -> s1 =s= s2 -> t1 .: s1 =s= t2 .: s2
| seq_subst_congr_comp s1 s2 r1 r2 : 
    s1 =s= s2 -> r1 =s= r2 -> s1 ∘ r1 =s= s2 ∘ r2
(* Sigma. *)
| seq_subst_id_left s :  S_id ∘ s =s= s 
| seq_subst_id_right s : s ∘ S_id =s= s 
| seq_subst_assoc s1 s2 s3 : s1 ∘ (s2 ∘ s3) =s= (s1 ∘ s2) ∘ s3
| seq_subst_distrib t s1 s2 : (t .: s1) ∘ s2 =s= t[: s2 ] .: s1 ∘ s2
| seq_subst_succ_cons t s : S_succ ∘ (t .: s) =s= s
where "t1 =t= t2" := (seq_term t1 t2)
  and "as1 =al= as2" := (seq_args _ as1 as2)
  and "a1 =a= a2" := (seq_arg _ a1 a2)
  and "s1 =s= s2" := (seq_subst s1 s2).

Hint Constructors seq_term  : core.
Hint Constructors seq_args  : core.
Hint Constructors seq_arg   : core.
Hint Constructors seq_subst : core.

Scheme seq_term_min  := Minimality for seq_term Sort Prop 
  with seq_args_min  := Minimality for seq_args Sort Prop 
  with seq_arg_min   := Minimality for seq_arg Sort Prop 
  with seq_subst_min := Minimality for seq_subst Sort Prop.  

Lemma seq_equiv : Equivalence seq_term.
Proof.
constructor.
- intros t. 
  apply (term_ind' 
    (fun t => t =t= t) (fun tys b => b =al= b) 
    (fun ty a => a =a= a) (fun s => s =s= s)).
  all: now auto.
- intros t1.
  apply (term_ind' 
    (fun t1 => forall t2, t1 =t= t2 -> t2 =t= t1) (fun _ a1 => forall a2, a1 =al= a2 -> a2 =al= a1)
    (fun _ a1 => forall a2, a1 =a= a2 -> a2 =a= a1) (fun s1 => forall s2, s1 =s= s2 -> s2 =s= s1)).
  +  
    all: try now auto.

  apply (seq_term_min
    (fun t1 t2 => t1 =t= t2 -> t2 =t= t1) (fun _ a1 a2 => a1 =al= a2 -> a2 =al= a1)
    (fun _ a1 a2 => a1 =a= a2 -> a2 =a= a1) (fun s1 s2 => s1 =s= s2 -> s2 =s= s1)).
  all: try now auto.
  + intros.
admit.
Admitted.

Instance eq_term_refl : Symmetric seq_term.
Proof.
intros t. 
apply (term_ind' (fun t => t =t= t) (fun ty a => a =a= a) (fun s => s =s= s)).
all: try (intros ; now constructor).
admit.
Admitted.



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

  

