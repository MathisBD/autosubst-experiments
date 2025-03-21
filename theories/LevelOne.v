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
  Proper (eq ==> pointwise_relation _ eq ==> eq) (@substitute so).
Proof. 
intros t ? <-. induction t ; intros s1 s2 Hs ; simpl ; try (now auto).
f_equal. apply IHt. now rewrite Hs.
Qed. 

(*********************************************************************************)
(** *** Properties of substitution. *)
(*********************************************************************************)

Lemma up_subst_sid : point_eq (up_subst sid) sid.
Proof. intros [|n] ; cbv [up_subst rshift] ; simpl ; auto. Qed. 

Lemma subst_id so (t : term so) : substitute t sid = t.
Proof.
induction t ; try (now auto).
simpl. now rewrite up_subst_sid, IHt.
Qed.

Lemma lift_subst so (t : term so) k : 
  lift k t = subst t (fun n => if Nat.ltb n k then T_var n else T_var (S n)).
Proof.
revert k. induction t ; intros k ; simpl ; try (now auto).
f_equal. rewrite IHt. apply subst_proper ; auto.
intros [|n] ; simpl ; auto.
destruct (PeanoNat.Nat.ltb_spec n k) ; destruct (PeanoNat.Nat.ltb_spec (S n) (S k)) ; 
simpl ; solve [ ltac1:(lia) | reflexivity ].
Qed.

Lemma subst_comp so (t : term so) s1 s2 : subst (subst t s1) s2 = subst t (scomp s2 s1).
Proof.
revert s1 s2. induction t ; intros s1 s2 ; simpl ; try (now auto).
f_equal. rewrite IHt. apply subst_proper ; auto.
intros n. cbv [scomp]. destruct n as [|n] ; simpl ; auto.
generalize (s1 n) ; intros t'.
Admitted.


End WithSig.