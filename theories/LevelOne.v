From Prototype Require Import Prelude Sig.

(** This file defines terms and substitutions over an abstract signature.
    Substitutions are represented as functions [nat -> term],
    and we prove the main properties of substitution. *)

Section WithSig.
Context {sig : Sig.t}.
Definition arg_ty := @Sig.arg_ty (Sig.base sig).

(*********************************************************************************)
(** *** Terms. *)
(*********************************************************************************)

(** Terms are indexed by (meta-level) sorts. 
    This is a trick to avoid encoding terms as a mutual inductive,
    and seems to be easier to work with. *)
Inductive sort := 
| T (* Term. *)
| A (a : arg_ty) (* Argument. *)
| AL (args : list arg_ty). (* Argument list. *)

(** Terms over an abstract signature. *)
Inductive term : sort -> Type :=
(** Terms. *)
| (* A term variable. *)
  T_var : nat -> term T
| (* A _non-variable_ term constructor, applied to a list of arguments. *)
  T_ctor : forall c, term (AL (Sig.ctor_type sig c)) -> term T
(** An argument list, of type [tys]. *)
| AL_nil : term (AL [])
| AL_cons {ty tys} : term (A ty) -> term (AL tys) -> term (AL (ty :: tys))
(** A single argument of type [ty]. *)
| A_base : forall b, Sig.denote_base sig b -> term (A (AT_base b))
| A_term : term T -> term (A AT_term)
| A_bind {ty} : term (A ty) -> term (A (AT_bind ty)).

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** A renaming on terms is a function [nat -> nat] which is applied
    to all free variables. *)
Definition ren := nat -> nat.

(** The identity renaming. *)
Definition rid : ren := fun n => n.

(** [rshift k] shifts indices by [k]. *)
Definition rshift (k : nat) : ren := fun n => n + k.

(** Cons an index with a renaming. *)
Definition rcons (n0 : nat) (r : ren) : ren :=
  fun n =>
    match n with 
    | 0 => n0
    | S n => r n
    end.
#[global] Instance rcons_notation : Scons nat ren :=
{ gen_scons := rcons }.

(** Compose two renamings (right to left composition). *)
Definition rcomp (r1 r2 : ren) : ren :=
  fun n => r1 (r2 n).
#[global] Instance rcomp_notation : Scomp ren :=
{ gen_scomp := rcomp }.

(** Lift a renaming through a binder. *)
Definition up_ren (r : ren) : ren := 0 .: rshift 1 ∘ r.
 
(** Rename a term. *)
Fixpoint rename {so} (t : term so) (r : ren) : term so :=
  match t with 
  | T_var n => T_var (r n)
  | T_ctor c args => T_ctor c (rename args r)
  | AL_nil => AL_nil
  | AL_cons a args => AL_cons (rename a r) (rename args r)
  | A_base b x => A_base b x
  | A_term t => A_term (rename t r)
  | A_bind a => A_bind (rename a (up_ren r))
  end.
#[global] Instance rename_notation so : Subst (term so) ren :=
{ gen_subst := rename }.
  
(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [nat -> term T] which is applied 
    to all free variables. *)
Definition subst := nat -> term T.

(** The identity substitution. *)
Definition sid : subst := fun n => T_var n.

(** [sshift k] shifts indices by [k]. *)
Definition sshift (k : nat) : subst := fun n => T_var (n + k).

(** Cons a term with a substitution. *)
Definition scons (t : term T) (s : subst) : subst :=
  fun n => 
    match n with 
    | 0 => t
    | S n => s n
    end.
#[global] Instance scons_notation : Scons (term T) subst :=
{ gen_scons := scons }.

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  T_var 0 .: (fun n => rename (s n) (rshift 1)).

(** Apply a substitution to a term. *)
Fixpoint substitute {so} (t : term so) (s : subst) : term so :=
  match t with 
  | T_var n => s n
  | T_ctor c args => T_ctor c (substitute args s)
  | AL_nil => AL_nil
  | AL_cons a args => AL_cons (substitute a s) (substitute args s)
  | A_base b x => A_base b x
  | A_term t => A_term (substitute t s)
  | A_bind a => A_bind (substitute a (up_subst s))
  end.
#[global] Instance substitute_notation so : Subst (term so) subst :=
{ gen_subst := substitute }.

(** Composition of substitutions (right to left). *)
Definition scomp (s1 s2 : subst) : subst :=
  fun n => substitute (s2 n) s1.
#[global] Instance scomp_notation : Scomp subst :=
{ gen_scomp := scomp }.

(*********************************************************************************)
(** *** Setoid Rewrite Support. *)
(*********************************************************************************)

(** Pointwise equality for functions. *)
Definition point_eq {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (point_eq f g) (at level 75).

#[global] Instance up_ren_proper : Proper (point_eq ==> point_eq) up_ren.
Proof. 
intros r1 r2 Hr [|n] ; cbv [up_ren] ; simpl.
- reflexivity.
- cbv [rcomp rshift]. auto.
Qed. 

#[global] Instance rename_proper so :
  Proper (eq ==> point_eq ==> eq) (@rename so).
Proof.
intros t ? <-. induction t ; intros s1 s2 Hs ; simpl ; try (now auto).
f_equal. apply IHt. now rewrite Hs.
Qed.

#[global] Instance up_subst_proper : Proper (point_eq ==> point_eq) up_subst.
Proof.
intros s1 s2 Hs [|n] ; cbv [up_subst] ; simpl.
- reflexivity.
- now rewrite Hs.
Qed. 

#[global] Instance substitute_proper so : 
  Proper (eq ==> point_eq ==> eq) (@substitute so).
Proof. 
intros t ? <-. induction t ; intros s1 s2 Hs ; simpl ; try (now auto).
f_equal. apply IHt. now rewrite Hs.
Qed. 

(*********************************************************************************)
(** *** Properties of substitution. *)
(*********************************************************************************)

Lemma rshift1 n : rshift 1 n = S n.
Proof. cbv [rshift]. lia. Qed.

Lemma up_ren_comp r1 r2 : 
  up_ren r1 ∘ up_ren r2 =₁ up_ren (r1 ∘ r2).
Proof.
intros [|n] ; simpl.
- reflexivity.
- cbv [rcomp up_ren]. simpl. cbv [rcomp rcons].
  repeat rewrite rshift1. reflexivity.
Qed.

Lemma ren_ren so (t : term so) (r1 r2 : ren) : 
  t[: r1][: r2] = t[: r2 ∘ r1].
Proof.
revert r1 r2. induction t ; intros r1 r2 ; simpl ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- setoid_rewrite IHt. now rewrite up_ren_comp.
Qed.

Lemma subst_ren so (t : term so) (s : subst) (r : ren) : 
  t[: s][: r] = t[: fun n => (s n)[: r]].
Proof.
revert s r. induction t ; intros s r ; simpl ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [reflexivity|].
  intros [|n] ; simpl ; [reflexivity|].
  cbv [up_subst]. simpl. repeat setoid_rewrite ren_ren.
  apply rename_proper ; [reflexivity|].
  intros [|n'] ; simpl ; [reflexivity|].
  cbv [rcomp up_ren]. simpl. repeat rewrite rshift1. cbv [rcomp].
  rewrite rshift1. reflexivity.
Qed.

Lemma ren_subst so (t : term so) (s : subst) (r : ren) : 
  t[: r][: s] = t[: fun n => s (r n)].
Proof.
revert s r. induction t ; intros s r ; simpl ; try (now auto).
- now setoid_rewrite IHt. 
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [reflexivity|].
  intros [|n] ; simpl ; [reflexivity|].
  cbv [up_subst up_ren]. simpl. cbv [scons rcomp].
  rewrite rshift1. reflexivity.
Qed.  

Lemma subst_subst so (t : term so) (s1 s2 : subst) : 
  t[: s1][: s2] = t[: s2 ∘ s1].
Proof.
revert s1 s2. induction t ; intros s1 s2 ; cbn ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. setoid_rewrite IHt2. reflexivity.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [auto | simpl].
  intros [|n] ; simpl ; [reflexivity|].
  cbv [scomp]. simpl. 
  setoid_rewrite subst_ren. setoid_rewrite ren_subst. simpl.
  apply substitute_proper ; [reflexivity|].
  intros n'. rewrite rshift1. reflexivity.
Qed.

Lemma up_subst_sid : (up_subst sid) =₁ sid.
Proof. intros [|n] ; cbv [up_subst rshift] ; simpl ; auto. Qed. 

Lemma subst_sid so (t : term so) : t[: sid] = t.
Proof.
induction t ; try (now auto).
simpl. rewrite up_subst_sid. now setoid_rewrite IHt.
Qed.

Lemma scomp_id_l s : sid ∘ s =₁ s.
Proof. intros n. simpl. cbv [scomp]. now setoid_rewrite subst_sid. Qed.
    
Lemma scomp_id_r s : s ∘ sid =₁ s.
Proof. intros n. simpl. cbv [scomp]. simpl. reflexivity. Qed.

Lemma scomp_assoc (s1 s2 s3 : subst) : (s1 ∘ s2) ∘ s3 =₁ s1 ∘ (s2 ∘ s3).
Proof. intros n. simpl. cbv [scomp]. now setoid_rewrite subst_subst. Qed.

End WithSig.