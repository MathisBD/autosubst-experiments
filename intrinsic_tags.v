From Coq Require Import String List Morphisms Relations.
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

Inductive sort := 
| S (* Substitution. *)
| T (* Term. *)
| A (a : arg_ty) (* Argument. *) 
| AL (args : list arg_ty). (* Argument list. *)

(** Terms from the sigma calculus. Terms are well-formed by construction,
    i.e. we enforce that constructors are applied to the right number 
    and types of arguments _intrinsically_ instead of _extrinsically_. *)
Inductive term : sort -> Type :=
| (* A term variable. *)
  T_var : nat -> term T
| (* A term constructor, applied to a list of arguments. *)
  T_ctor : forall c, term (AL (ctor_type c)) -> term T
| (* An explicit substitution, applied to a term. *)
  T_subst : term T -> term S -> term T
(** A list of arguments of type [tys]. *)
| AL_nil : term (AL [])
| AL_cons {ty tys} : term (A ty) -> term (AL tys) -> term (AL (ty :: tys))
(** A single argument of type [ty]. *)
| A_base : forall b, base_type b -> term (A (AT_base b))
| A_term : term T -> term (A AT_term)
| A_bind {ty} : term (A ty) -> term (A (AT_bind ty))
(** Explicit substitutions. *)
| (* The successor subsitution: it maps [n] to [n+1]. *)
  S_succ : term S
| S_cons : term T -> term S -> term S
| (* [S_comp s1 s2] applies [s2] followed by [s1]. 
     It is equivalent to [s1 ∘ s2]. *)
  S_comp : term S -> term S -> term S.

(* Custom notations to ease writing terms and substitutions. *)
Notation "t .: s" := (S_cons t s) (at level 70, right associativity).
Notation "s1 ∘ s2" := (S_comp s1 s2) (at level 50, left associativity).
Notation "t '[:' s ']'" := (T_subst t s) (at level 40, s at level 0, no associativity).

(** The identity substitution. *)
Definition S_id : term S := T_var 0 .: S_succ.

Fixpoint a_subst {ty : arg_ty} (a : term (A ty)) (s : term S) : term (A ty) :=
  match a with 
  | A_base b x => A_base b x
  | A_term t => A_term (t[: s])
  | A_bind a' => A_bind (a_subst a' (T_var 0 .: S_succ ∘ s))
  end.

Fixpoint al_subst {tys : list arg_ty} (al : term (AL tys)) (s : term S) : term (AL tys) :=
  match al with 
  | AL_nil => AL_nil
  | AL_cons a al => AL_cons (a_subst a s) (al_subst al s)
  end.

(** [t σ= t'] means that the terms/substitutions [t] and [t'] are equal 
    modulo the equational theory of sigma calculus. *)
Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
Inductive seq : forall s, term s -> term s -> Prop :=

(** Equivalence. *)

| seq_refl s (t : term s) : t =σ t
| seq_sym s (t1 t2 : term s) : t1 =σ t2 -> t2 =σ t1
| seq_trans s (t1 t2 t3 : term s) : t1 =σ t2 -> t2 =σ t3 -> t1 =σ t3

(** Congruence. *)

| seq_t_ctor c args1 args2 : 
    args1 =σ args2 -> T_ctor c args1 =σ T_ctor c args2
| seq_t_subst t1 t2 s1 s2 : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 

| seq_al_cons ty tys (a1 a2 : term (A ty)) (b1 b2 : term (AL tys)) : 
    a1 =σ a2 -> b1 =σ b2 -> AL_cons a1 b1 =σ AL_cons a2 b2
(*| seq_al_subst tys (a1 a2 : term (AL tys)) s1 s2 :
    a1 =σ a2 -> s1 =σ s2 -> AL_subst a1 s1 =σ AL_subst a2 s2*)

| seq_a_term t1 t2 : t1 =σ t2 -> A_term t1 =σ A_term t2
| seq_a_bind ty (a1 a2 : term (A ty)) : a1 =σ a2 -> A_bind a1 =σ A_bind a2
(*| seq_a_subst ty (a1 a2 : term (A ty)) s1 s2 : 
    a1 =σ a2 -> s1 =σ s2 -> a1[. s1 ] =σ a2[. s2 ]*)

| seq_s_cons t1 t2 s1 s2 : 
    t1 =σ t2 -> s1 =σ s2 -> t1 .: s1 =σ t2 .: s2
| seq_s_comp s1 s2 r1 r2 : 
    s1 =σ s2 -> r1 =σ r2 -> s1 ∘ r1 =σ s2 ∘ r2

(** Sigma equations. *)

| seq_push_subst c args s : (T_ctor c args)[: s] =σ T_ctor c (al_subst args s)
(*| seq_push_subst_ctor c args s : (T_ctor c args)[: s ] =σ T_ctor c (args[, s])
| seq_push_subst_args ty tys (a : term (A ty)) (b : term (AL tys)) s :
    (AL_cons a b)[, s ] =σ AL_cons (a[.s]) (b[,s])
| seq_push_subst_term t s :
    (A_term t)[. s] =σ A_term (t[: s])
| seq_push_subst_bind ty (a : term (A ty)) s : 
    (A_bind a)[. s ] =σ A_bind (a[. T_var 0 .: s ∘ S_succ ])
| seq_push_subst_base b x s :
    (A_base b x)[. s] =σ A_base b x*)

| seq_zero_cons s t : (T_var 0)[: t .: s ] =σ t
| seq_id_left s :  S_id ∘ s =σ s 
| seq_id_right s : s ∘ S_id =σ s 
| seq_assoc s1 s2 s3 : s1 ∘ (s2 ∘ s3) =σ (s1 ∘ s2) ∘ s3
| seq_distrib t s1 s2 : (t .: s1) ∘ s2 =σ t[: s2 ] .: s1 ∘ s2
| seq_succ_cons t s : S_succ ∘ (t .: s) =σ s

where "t1 '=σ' t2" := (seq _ t1 t2).
Hint Constructors seq  : core.

(** *** Setoid rewrite support. *)

Instance seq_equiv s : Equivalence (seq s).
Proof. constructor ; eauto. Qed.

Instance t_subst_proper : Proper (seq T ==> seq S ==> seq T) T_subst.
Proof. intros ? ? ? ? ? ?. auto. Qed.

(* TODO : other instances. *)
    
End AbstractTerms.

(** *** Example : lambda calculus. *)

(** Concrete terms. 
    Applications carry a boolean.
    Lambda abstractions contain the name of the bound variable as a string. *)
Inductive cterm :=
  | Var : nat -> cterm
  | App : bool -> cterm -> cterm -> cterm
  | Lam : string -> cterm -> cterm.

(** Basic substitutions. *)
Definition csucc (n : nat) : cterm := Var (S n).
Definition ccons (t : cterm) (s : nat -> cterm) (n : nat) : cterm :=
  match n with 
  | 0 => t
  | S n => s n
  end.

Fixpoint lift k (t : cterm) : cterm :=
  match t with 
  | Var n => if Nat.ltb n k then Var n else Var (S n)
  | App b t1 t2 => App b (lift k t1) (lift k t2)
  | Lam str t => Lam str (lift (S k) t)
  end.

(** Concrete substitution function. *)
Fixpoint csubst (t : cterm) (s : nat -> cterm) {struct t} : cterm :=
  match t with 
  | Var n => s n
  | App b t1 t2 => App b (csubst t1 s) (csubst t2 s)
  | Lam str t => 
    let s := ccons (Var 0) (fun n => lift 0 (s n)) in
    Lam str (csubst t s)
  end.

Definition ccomp (s1 : nat -> cterm) (s2 : nat -> cterm) (n : nat) : cterm :=
  csubst (s2 n) s1.

Instance csubst_proper : Proper (eq ==> pointwise_relation nat eq ==> eq) csubst.
Proof.
intros t ? <-. induction t ; intros s1 s2 Hs ; simpl.
- auto.
- f_equal ; auto.
- f_equal. apply IHt. intros [|n] ; simpl.
  + reflexivity.
  + now rewrite Hs.
Qed.  

(** Abstract signature. *)

Module S.
  Inductive base_ := BString | BBool.
  Definition base := base_.
  
  Definition base_type (b : base) : Type :=
    match b with BString => string | BBool => bool end.
  
  Inductive ctor_ := CApp | CLam. 
  Definition ctor := ctor_. 

  Definition ctor_type (c : ctor) : list arg_ty :=
    match c with 
    | CApp => [ AT_base BBool ; AT_term ; AT_term ]
    | CLam => [ AT_base BString ; AT_bind (AT_term) ]
    end.
End S.

(** Abstract terms. *)
Module A := AbstractTerms (S).
Import A.
Definition aterm := term T.

(** Mapping from concrete terms to abstract terms. *)
Fixpoint reify (t : cterm) : aterm :=
  match t with 
  | Var n => T_var n
  | App b t1 t2 => 
    T_ctor CApp 
      (AL_cons (A_base BBool b) 
      (AL_cons (A_term (reify t1)) 
      (AL_cons (A_term (reify t2))
       AL_nil)))
  | Lam s t => 
    T_ctor CLam 
      (AL_cons (A_base BString s) 
      (AL_cons (A_bind (A_term (reify t)))
       AL_nil))
  end.

(**************)
Section DenoteSort.
  (* Denotation for [term]. *)
  Context (denote_term : Type).

  (** Denote argument types into [Type]. *)
  Fixpoint denote_arg_ty (ty : arg_ty) : Type :=
    match ty with 
    | AT_base b => base_type b
    | AT_term => denote_term
    | AT_bind ty => denote_arg_ty ty
    end.

  (** Denote the type of a term constructor with arguments in [tys].
      We build the (non-dependent) arrow [ty0 -> ty1 -> ... -> term]. *)
  Fixpoint denote_al_ty (tys : list arg_ty) : Type :=
    match tys with 
    | [] => denote_term
    | ty :: tys => denote_arg_ty ty -> denote_al_ty tys
    end.

  Definition denote_sort (s : sort) : Type :=
    match s with 
    | S => nat -> denote_term
    | T => denote_term
    | AL tys => denote_al_ty tys -> denote_term
    | A ty => denote_arg_ty ty
    end.
End DenoteSort.
(**************)

Definition denote_ctor (c : ctor) : denote_al_ty cterm (ctor_type c) :=
  match c with 
  | CApp => App
  | CLam => Lam
  end.

(** Mapping from abstract terms to concrete terms. 
    This uses some continuation passing style (when denoting argument lists). *)
Fixpoint denote {s} (t : A.term s) : denote_sort cterm s :=
  match t in A.term s0 return denote_sort cterm s0  with
  | S_succ => csucc
  | S_cons t s => ccons (denote t) (denote s)
  | S_comp s1 s2 => ccomp (denote s1) (denote s2)
  | T_var n => Var n 
  | T_ctor c args => (denote args) (denote_ctor c)
  | T_subst t s => csubst (denote t) (denote s)
  | AL_nil => fun t => t
  | AL_cons a args => fun f => (denote args) (f (denote a))
  (*| AL_subst args s => _
    (*(denote args : (T1 -> T2 -> ... -> cterm) -> cterm) (csubst . (denote s) : cterm -> cterm)
    fun f => g . f*)*)
  | A_base b x => x
  | A_term t => denote t
  | A_bind a => denote a
  (*| A_subst a s => (denote a : denote_arg_ty ty) (denote s : nat -> cterm) (*csubst (denote a) (denote s)*)*)
  end.


Definition sort_rel (s : sort) : relation (denote_sort cterm s) :=
  match s with 
  | S => pointwise_relation _ eq
  | T => eq
  | A ty => eq
  | AL tys => pointwise_relation _ eq
  end.

Instance sort_rel_equiv s : Equivalence (sort_rel s).
Proof.
destruct s ; simpl ; constructor ; auto.
all: intros ? ; etransitivity ; now eauto.
Qed.

Lemma denote_sound {s} : Proper (seq s ==> sort_rel s) denote.
Proof.
intros t1 t2 Ht. induction Ht ; simpl in * ; try now auto.
- etransitivity ; eauto.
- now rewrite IHHt1, IHHt2.
- rewrite IHHt1. intros f. auto.
- intros [|n] ; simpl ; auto.
- intros n ; cbv [ccomp]. now rewrite IHHt1, IHHt2.
- admit. (* TODO : push subst. *) 
- intros n ; cbv [ccomp].  

(*with denote_args {tys} (hd : denote_ctor_ty cterm tys) (args : arg_list tys) : cterm :=
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
  end.*)

  

