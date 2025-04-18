From Prototype Require Import Prelude Sig.

(** This file defines exprs and substitutions over an abstract signature.
    Substitutions are represented as functions [nat -> term],
    and we prove the main properties of substitution. *)

Module Make (S : Sig).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Terms. *)
(*********************************************************************************)

(** Terms are indexed by (meta-level) kinds. *)
Inductive kind := 
| (** Term. *)
  Kt : kind
| (** Constructor argument. *)
  Ka : arg_ty -> kind
| (** List of constructor arguments. *)
  Kal : list arg_ty -> kind.
Derive NoConfusion for kind.

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Terms over an abstract signature. 
    Terms are indexed by a kind. *)
Inductive expr : kind -> Type :=
| (** Term variable. *)
  E_var : nat -> term
| (** Non-variable expr constructor, applied to a list of arguments. *)
  E_ctor : forall c, args (ctor_type S.t c) -> term
| (** Empty argument list. *)
  E_al_nil : args []
| (** Non-empty argument list. *)
  E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)
| (** Base argument (e.g. bool or string). *)
  E_abase : forall b, denote_base S.t b -> arg (AT_base b)
| (** Term argument. *)
  E_aterm : term -> arg AT_term
| (** Binder argument. *)
  E_abind {ty} : arg ty -> arg (AT_bind ty)
where "'term'" := (expr Kt)
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** A renaming on terms is a function [nat -> nat] which is applied
    to all free variables. *)
Definition ren := nat -> nat.

(** The identity renaming. *)
Definition rid : ren := fun i => i.

(** [rshift k] shifts indices by [k]. *)
Definition rshift (k : nat) : ren := fun i => k + i.

(** Cons an index with a renaming. *)
Equations rcons (i0 : nat) (r : ren) : ren :=
rcons i0 _ 0 := i0 ;
rcons i0 r (S i) := r i.

(** Compose two renamings (left to right composition). *)
Definition rcomp (r1 r2 : ren) : ren :=
  fun i => r2 (r1 i).

(** Lift a renaming through a binder. *)
Definition up_ren (r : ren) : ren := 
  rcons 0 (rcomp r (rshift 1)).
 
(** Rename a term. *)
Equations rename {k} (t : expr k) (r : ren) : expr k :=
rename (E_var i) r := E_var (r i) ;
rename (E_ctor c al) r := E_ctor c (rename al r) ;
rename E_al_nil r := E_al_nil ;
rename (E_al_cons a al) r := E_al_cons (rename a r) (rename al r) ;
rename (E_abase b x) r := E_abase b x ;
rename (E_aterm t) r := E_aterm (rename t r) ;
rename (E_abind a) r := E_abind (rename a (up_ren r)).

(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [nat -> term] which is applied 
    to all free variables. *)
Definition subst := nat -> term.

(** The identity substitution. *)
Definition sid : subst := fun i => E_var i.

(** [sshift k] shifts indices by [k]. *)
Definition sshift (k : nat) : subst := 
  fun i => E_var (k + i).

(** Cons a expr with a substitution. *)
Equations scons (t : term) (s : subst) : subst :=
scons t s 0 := t ;
scons t s (S i) := s i.

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  scons (E_var 0) (fun i => rename (s i) (rshift 1)).

(** Apply a substitution to a expr. *)
Equations substitute {k} (t : expr k) (s : subst) : expr k :=
substitute (E_var i) s := s i ;
substitute (E_ctor c al) s := E_ctor c (substitute al s) ;
substitute E_al_nil s := E_al_nil ;
substitute (E_al_cons a al) s := E_al_cons (substitute a s) (substitute al s) ;
substitute (E_abase b x) s := E_abase b x ;
substitute (E_aterm t) s := E_aterm (substitute t s) ;
substitute (E_abind a) s := E_abind (substitute a (up_subst s)).

(** Left to right composition of substitutions. *)
Definition scomp (s1 s2 : subst) : subst :=
  fun i => substitute (s1 i) s2.

(*********************************************************************************)
(** *** Setoid Rewrite Support. *)
(*********************************************************************************)

#[global] Instance up_ren_proper : Proper (point_eq ==> point_eq) up_ren.
Proof. 
intros r1 r2 Hr i. destruct i ; cbv [rcons up_ren rcomp].
- reflexivity.
- now rewrite Hr.
Qed. 

#[global] Instance rcons_proper : Proper (eq ==> point_eq ==> point_eq) rcons.
Proof. intros i1 i2 it s1 s2 Hs i. destruct i ; simp rcons. now rewrite Hs. Qed.

#[global] Instance rcomp_proper : Proper (point_eq ==> point_eq ==> point_eq) rcomp.
Proof. 
intros s1 s2 Hs r1 r2 Hr i. destruct i ; cbv [rcomp].
- now rewrite Hs, Hr.
- now rewrite Hs, Hr.
Qed.

#[global] Instance rename_proper k :
  Proper (eq ==> point_eq ==> eq) (@rename k).
Proof.
intros t _ <- r1 r2 Hr. funelim (rename t _) ; simp rename in * ; auto.
f_equal. apply H. now rewrite Hr.
Qed.

#[global] Instance up_subst_proper : Proper (point_eq ==> point_eq) up_subst.
Proof.
intros s1 s2 Hs i. destruct i ; cbv [up_subst scons].
- reflexivity.
- now rewrite Hs.
Qed. 

#[global] Instance scons_proper : Proper (eq ==> point_eq ==> point_eq) scons.
Proof. 
intros t1 t2 Ht s1 s2 Hs i. 
destruct i ; simp scons. now rewrite Hs. 
Qed.
    
#[global] Instance substitute_proper k : 
  Proper (eq ==> point_eq ==> eq) (@substitute k).
Proof. 
intros t ? <- s1 s2 Hs. funelim (substitute t _) ; simp substitute in * ; auto.
f_equal. apply H. now rewrite Hs.
Qed. 

#[global] Instance scomp_proper : Proper (point_eq ==> point_eq ==> point_eq) scomp.
Proof. 
intros s1 s2 Hs r1 r2 Hr i. destruct i ; cbv [scomp].
- now rewrite Hs, Hr.
- now rewrite Hs, Hr.
Qed.

(*********************************************************************************)
(** *** Properties of substitution. *)
(*********************************************************************************)

Lemma up_ren_comp (r1 r2 : ren) : 
  rcomp (up_ren r1) (up_ren r2) =₁ up_ren (rcomp r1 r2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma ren_ren {k} (t : expr k) (r1 r2 : ren) : 
  rename (rename t r1) r2 = rename t (rcomp r1 r2).
Proof.
funelim (rename t _) ; simp rename in * ; auto.
now rewrite H, up_ren_comp.
Qed.

Lemma subst_ren {k} (t : expr k) (s : subst) (r : ren) : 
  rename (substitute t s) r = substitute t (fun i => rename (s i) r).
Proof.
funelim (substitute t _) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; auto. cbv [up_subst scons].
rewrite ren_ren, ren_ren. apply rename_proper ; auto.
reflexivity.
Qed.

Lemma ren_subst {k} (t : expr k) (r : ren) (s : subst) : 
  substitute (rename t r) s = substitute t (fun i => s (r i)).
Proof.
funelim (rename t r) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; reflexivity.
Qed.

Lemma up_subst_comp (s1 s2 : subst) : 
  scomp (up_subst s1) (up_subst s2) =₁ up_subst (scomp s1 s2).
Proof. 
intros [|i] ; auto. cbv [up_subst scomp]. simp scons.
rewrite ren_subst, subst_ren. apply substitute_proper ; auto.
intros i'. reflexivity.
Qed.

Lemma subst_subst {k} (t : expr k) (s1 s2 : subst) : 
  substitute (substitute t s1) s2 = substitute t (scomp s1 s2).
Proof.
funelim (substitute t _) ; simp substitute ; auto.
rewrite H. now rewrite up_subst_comp.
Qed.

Lemma up_subst_sid : up_subst sid =₁ sid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma subst_sid {k} (t : expr k) : substitute t sid = t.
Proof.
induction t ; simp substitute in * ; auto.
rewrite up_subst_sid. auto.
Qed.

Lemma scomp_id_l (s : subst) : scomp sid s =₁ s.
Proof. reflexivity. Qed.

Lemma scomp_id_r (s : subst) : scomp s sid =₁ s.
Proof. intros i. cbv [scomp]. now rewrite subst_sid. Qed.

Lemma scomp_assoc (s1 s2 s3 : subst) : 
  scomp (scomp s1 s2) s3 =₁ scomp s1 (scomp s2 s3).
Proof. intros i. cbv [scomp]. now rewrite subst_subst. Qed.

Lemma ren_is_subst {k} (t : expr k) (r : ren) : 
  rename t r = substitute t (fun i => E_var (r i)).
Proof.
funelim (rename t r) ; simp rename substitute ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; reflexivity.
Qed.

Lemma rshift_sshift {k} (t : expr k) : 
  rename t (rshift 1) = substitute t (sshift 1).
Proof. rewrite ren_is_subst. reflexivity. Qed.
    
Lemma up_subst_alt (s : subst) :
  up_subst s =₁ scons (E_var 0) (scomp s (sshift 1)).
Proof.
simp up_subst. apply scons_proper ; auto.
intros i. cbv [scomp]. now rewrite rshift_sshift.
Qed.

Lemma sshift_succ_r k : sshift (S k) =₁ scomp (sshift k) (sshift 1).
Proof. intros [|i] ; reflexivity. Qed.

Lemma sid_scons : scons (E_var 0) (sshift 1) =₁ sid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma scomp_scons_distrib (t : term) (s1 s2 : subst) :
  scomp (scons t s1) s2 =₁ scons (substitute t s2) (scomp s1 s2).
Proof. intros [|i] ; reflexivity. Qed.

End Make.