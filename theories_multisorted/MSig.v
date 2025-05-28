(** This file defines the notion of abstract signature of a language. *)

From Prototype Require Import MPrelude.

(*********************************************************************************)
(** *** Signatures. *)
(*********************************************************************************)

(** Argument types over a set of base types and a set of sorts. *)
Inductive arg_ty {nbase nsort} :=
| AT_base : fin nbase -> arg_ty
| AT_term : fin nsort -> arg_ty
| AT_bind : fin nsort -> fin nsort -> arg_ty.
Derive NoConfusion NoConfusionHom for arg_ty.

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

(*********************************************************************************)
(** *** Computing properties of signatures. *)
(*********************************************************************************)

Section Signature.
Context {sig : signature}.

(** [occurs_ty] *)

Inductive occurs_ty (s : fin nsort) : @arg_ty nbase nsort -> Prop :=
| occurs_ty_term : occurs_ty s (AT_term s)
| occurs_ty_bind {s1} : occurs_ty s (AT_bind s1 s).
Derive Signature for occurs_ty.

Equations occurs_tyb : fin nsort -> @arg_ty nbase nsort -> bool :=
occurs_tyb s (AT_base _) := false ;
occurs_tyb s (AT_term s') := eqb_fin s s' ;
occurs_tyb s (AT_bind _ s') := eqb_fin s s'.

Lemma occurs_ty_spec s ty : reflect (occurs_ty s ty) (occurs_tyb s ty).
Proof.
funelim (occurs_tyb s ty).
- right. intros H. depelim H.
- destruct (eqb_fin_spec s s') ; subst.
  + left. constructor.
  + right. intros H. now depelim H.
- destruct (eqb_fin_spec s s') ; subst.
  + left. constructor.
  + right. intros H. now depelim H.
Qed.

(** [occurs_direct] *)

Definition occurs_direct (s s' : fin nsort) : Prop :=
  exists c : fin (nctor s'), Exists (occurs_ty s) (ctor_type c).

Definition occurs_directb (s s' : fin nsort) : bool :=
  fin_existsb (nctor s') (fun c => existsb (occurs_tyb s) (ctor_type c)).
  
Lemma occurs_direct_spec s s' : reflect (occurs_direct s s') (occurs_directb s s').
Proof.
unfold occurs_directb. 
destruct (fin_existsb_spec (nctor s') (fun c => existsb (occurs_tyb s) (ctor_type c))).
- left. destruct e as (i & H). exists i. rewrite Exists_exists.
  unfold is_true in H. rewrite existsb_exists in H. destruct H as (ty & H1 & H2).
  exists ty. split ; [assumption|]. now destruct (occurs_ty_spec s ty).
- right. intros H. apply n. clear n. destruct H as (i & H). rewrite Exists_exists in H.
  destruct H as (ty & H1 & H2). exists i. unfold is_true. rewrite existsb_exists.
  exists ty. split ; [assumption|]. now destruct (occurs_ty_spec s ty).
Qed. 

(** [occurs s s'] : [s] occurs in [s'] (reflexive-transitive closure of [occurs_direct]). *)

Inductive occurs : fin nsort -> fin nsort -> Prop :=
| occurs_refl s : occurs s s
| occurs_base s s' : occurs_direct s s' -> occurs s s'
| occurs_trans s s' s'' : occurs s s' -> occurs s' s'' -> occurs s s''.

Equations occursb_aux : nat -> fin nsort -> fin nsort -> bool :=
occursb_aux 0 s s' := occurs_directb s s' ;
occursb_aux (S n) s s' := fin_existsb nsort (fun s1 => occurs_directb s s1 && occursb_aux n s1 s').

Definition occursb (s s' : fin nsort) : bool := occursb_aux nsort s s'.

Lemma occurs_spec s s' : reflect (occurs s s') (occursb s s').
Proof. Admitted.

(** [binds_ty] *)

Inductive binds_ty (s : fin nsort) : @arg_ty nbase nsort -> Prop :=
| binds_ty_bind {s'} : binds_ty s (AT_bind s s').
Derive Signature for binds_ty.

Equations binds_tyb : fin nsort -> @arg_ty nbase nsort -> bool :=
binds_tyb s (AT_bind s' _) := eqb_fin s s' ;
binds_tyb _ _ := false.

Lemma binds_ty_spec s ty : reflect (binds_ty s ty) (binds_tyb s ty).
Proof.
funelim (binds_tyb s ty).
- right. intros H ; depelim H.
- right. intros H ; depelim H.
- destruct (eqb_fin_spec s s').
  + subst. left. constructor.
  + right. intros H. now depelim H.
Qed.

(** [binds s s'] : [s] is bound in [s'] (non-transitively). *)

Definition binds (s s' : fin nsort) : Prop := 
  exists c : fin (nctor s'), Exists (binds_ty s) (ctor_type c).

Definition bindsb (s s' : fin nsort) : bool := 
  fin_existsb (nctor s') (fun c => existsb (binds_tyb s) (ctor_type c)).

Lemma binds_spec s s' : reflect (binds s s') (bindsb s s').
Proof.
unfold bindsb. 
destruct (fin_existsb_spec (nctor s') (fun c => existsb (binds_tyb s) (ctor_type c))).
- left. destruct e as (i & H). exists i. rewrite Exists_exists.
  unfold is_true in H. rewrite existsb_exists in H. destruct H as (ty & H1 & H2).
  exists ty. split ; [assumption|]. now destruct (binds_ty_spec s ty).
- right. intros H. apply n. clear n. destruct H as (i & H). rewrite Exists_exists in H.
  destruct H as (ty & H1 & H2). exists i. unfold is_true. rewrite existsb_exists.
  exists ty. split ; [assumption|]. now destruct (binds_ty_spec s ty).
Qed. 

(** [has_var] *)

Definition has_var (s : fin nsort) : Prop :=
  exists s', binds s s' /\ occurs s s'.
  
Definition has_varb (s : fin nsort) : bool := 
  fin_existsb nsort (fun s' => bindsb s s' && occursb s s').

Lemma has_var_spec s : reflect (has_var s) (has_varb s).
Proof. 
unfold has_varb. 
destruct (fin_existsb_spec nsort (fun s' => bindsb s s' && occursb s s')).
- left. destruct e as (s' & H). exists s'. 
  now destruct (binds_spec s s'), (occurs_spec s s').
- right. intros H. apply n. clear n. destruct H as (s' & H). exists s'.
  now destruct (binds_spec s s'), (occurs_spec s s').
Qed.

End Signature.
