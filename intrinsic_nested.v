From Coq Require Import String List Morphisms.
Import ListNotations.

(** Ordinals. *)
Record Ordinal n := { ordinal_i : nat ; ordinal_lt_n : ordinal_i < n }.
Notation "''I_' n" := (Ordinal n) (at level 8, n at level 2, format "''I_' n").

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Heterogeneous lists: the elements of the lists can have different types. *)
Inductive hlist {A} (P : A -> Type) : list A -> Type :=
| hnil : hlist P []
| hcons {x xs} : P x -> hlist P xs -> hlist P (x :: xs).
Arguments hnil {A} {P}.
Arguments hcons {A} {P} {x} {xs} _ _.
#[global] Hint Constructors hlist : core.

Fixpoint hmap {A} {P Q : A -> Type} (f : forall x, P x -> Q x) {xs : list A} (l : hlist P xs) : hlist Q xs :=
  match l with 
  | hnil => hnil
  | hcons hd tl => hcons (f _ hd) (hmap f tl) 
  end.

Fixpoint hmap2 {A} {P Q R : A -> Type} (f : forall x, P x -> Q x -> R x) {xs : list A} 
  (l : hlist P xs) (l' : hlist Q xs) : hlist R xs.
Admitted. (* TODO : do the inversion by hand. *)
  (*match l with 
  | hnil, hnil => hnil
  | hcons hd tl, hcons hd' tl' => hcons (f _ hd hd') (hmap f tl tl')
  | _ => tt
  end.*)

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

(** Explicit substitutions. *)
Inductive subst (term : Type) : Type :=
| (* The successor subsitution: it maps [n] to [n+1]. *)
  S_succ : subst term
| (* [S_cons t s] maps [0] to [t] and [n+1] to [s n]. *)
  S_cons : term -> subst term -> subst term
| (* [S_comp s1 s2] maps [n] to [s2 (s1 n)]. *)
  S_comp : subst term -> subst term -> subst term.
Arguments S_succ {term}.
Arguments S_cons {term} _ _.
Arguments S_comp {term} _ _.

(** Constructor arguments. *)
Inductive arg (term : Type) : arg_ty -> Type :=
| A_base : forall b, base_type b -> arg term (AT_base b)
| A_term : term -> arg term AT_term
| A_bind {ty} : arg term ty -> arg term (AT_bind ty)
| A_subst {ty} : arg term ty -> subst term -> arg term ty.
Arguments A_base {term} _ _.
Arguments A_term {term} _.
Arguments A_bind {term} {ty} _.
Arguments A_subst {term} {ty} _ _.

(** Terms. *)
Inductive term : Type :=
| (* A term variable. *)
  T_var : nat -> term
| (* A term constructor, applied to a list of arguments. *)
  T_ctor : forall c, hlist (arg term) (ctor_type c) -> term
| (* An explicit substitution, applied to a term. *)
  T_subst : term -> subst term -> term.

(** Notations to ease writing terms and substitutions. *)
Notation "t .: s" := (S_cons t s) (at level 70, right associativity).
Notation "s1 ∘ s2" := (S_comp s1 s2) (at level 50, left associativity).
Notation "t '[:' s ']'" := (T_subst t s) (at level 40, s at level 0, no associativity).
Notation "a '[.' s ']'" := (A_subst a s) (at level 40, s at level 0, no associativity).

(** The identity substitution. *)
Definition S_id : subst term := T_var 0 .: S_succ.

(** Equality of substitutions. *)
Section Eq_subst.
  Context (eq_term : term -> term -> Prop).
  Notation "t1 =t= t2" := (eq_term t1 t2) (at level 75).
  
  Reserved Notation "s1 =s= s2" (at level 75).
  Inductive eq_subst : subst term -> subst term -> Prop :=
  (* Congruence. *)
  | eq_subst_congr_succ : S_succ =s= S_succ
  | eq_subst_congr_cons t1 t2 s1 s2 : 
      t1 =t= t2 -> s1 =s= s2 -> t1 .: s1 =s= t2 .: s2
  | eq_subst_congr_comp s1 s2 r1 r2 : 
      s1 =s= s2 -> r1 =s= r2 -> s1 ∘ r1 =s= s2 ∘ r2
  (* Symmetry. *)
  | eq_subst_sym s1 s2 : s1 =s= s2 -> s2 =s= s1
  (* Transitivity. *)
  | eq_subst_trans s1 s2 s3 : s1 =s= s2 -> s2 =s= s3 -> s1 =s= s3
  (* Sigma equations. *)
  | eq_subst_id_left s :  S_id ∘ s =s= s 
  | eq_subst_id_right s : s ∘ S_id =s= s 
  | eq_subst_assoc s1 s2 s3 : s1 ∘ (s2 ∘ s3) =s= (s1 ∘ s2) ∘ s3
  | eq_subst_distrib t s1 s2 : (t .: s1) ∘ s2 =s= t[: s2 ] .: s1 ∘ s2
  | eq_subst_succ_cons t s : S_succ ∘ (t .: s) =s= s
  where "s1 =s= s2" := (eq_subst s1 s2).

  #[global] Instance eq_subst_equiv : Equivalence eq_term -> Equivalence eq_subst.
  Proof.
  intros Hequiv. constructor.
  - intros t. induction t ; constructor ; solve [ auto | reflexivity ].
  - exact eq_subst_sym.
  - exact eq_subst_trans.
  Qed.
End Eq_subst.

(** Equality of arguments. *)
Section Eq_arg.
  Context (eq_term : term -> term -> Prop).
  Context (eq_subst : subst term -> subst term -> Prop).
  Notation "t1 =t= t2" := (eq_term t1 t2) (at level 75).
  Notation "s1 =s= s2" := (eq_subst s1 s2) (at level 75).

  Reserved Notation "a1 =a= a2" (at level 75).
  Inductive eq_arg : forall ty, arg term ty -> arg term ty -> Prop :=
  (* Congruence. *)
  | eq_arg_congr_base b x : A_base b x =a= A_base b x 
  | eq_arg_congr_term t1 t2 : t1 =t= t2 -> A_term t1 =a= A_term t2
  | eq_arg_congr_bind ty (a1 a2 : arg term ty) : a1 =a= a2 -> A_bind a1 =a= A_bind a2
  | eq_arg_congr_subst ty (a1 a2 : arg term ty) s1 s2 : 
      a1 =a= a2 -> s1 =s= s2 -> a1[. s1 ] =a= a2[. s2 ]
  (* Symmetry. *)
  | eq_arg_sym ty (a1 a2 : arg term ty) : a1 =a= a2 -> a2 =a= a1
  (* Transitivity. *)
  | eq_arg_trans ty (a1 a2 a3 : arg term ty) : a1 =a= a2 -> a2 =a= a3 -> a1 =a= a3
  (* Sigma equations. *) 
  | eq_arg_bind ty (a : arg term ty) s : 
      (A_bind a)[. s ] =a= A_bind (a[. T_var 0 .: s ∘ S_succ ])
  where "a1 =a= a2" := (eq_arg _ a1 a2).
    
  #[global] Instance eq_arg_equiv ty : 
    Equivalence eq_subst -> Equivalence eq_term -> Equivalence (eq_arg ty).
  Proof.
  intros H1 H2. constructor.
  - intros a. induction a ; constructor ; solve [auto | reflexivity]. 
  - intros a1 a2 Ha. now apply eq_arg_sym.
  - intros ? ? ? ? ?. eapply eq_arg_trans ; eauto.
  Qed. 
End Eq_arg.

Section Eq_term.
  Reserved Notation "t1 =t= t2" (at level 75).
  Inductive eq_term : term -> term -> Prop :=
  (* Congruence. *)
  | eq_term_congr_var n : T_var n =t= T_var n
  | eq_term_congr_ctor c args1 args2 : 
      hmap2 (eq_arg eq_term (eq_subst eq_term)) args1 args2 -> T_ctor c args1 =t= T_ctor c args2
  | eq_term_congr_subst t1 t2 s1 s2 : 
      t1 =t= t2 -> s1 =s= s2 -> t1[: s1 ] =t= t2[: s2 ] 
  (* Symmetry. *)
  | eq_term_sym t1 t2 : t1 =t= t2 -> t2 =t= t1
  (* Transitivity. *)
  | eq_term_trans t1 t2 t3 : t1 =t= t2 -> t2 =t= t3 -> t1 =t= t3
  (* Sigma. *)
  | eq_term_zero_cons s t : (T_var 0)[: t .: s ] =t= t
  | eq_term_push_subst c args s : 
      (T_ctor c args)[: s ] =t= T_ctor c (hmap (fun _ a => a[.s]) args)
  where "t1 =t= t2" := (eq_term t1 t2).


End Eq_term.

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
