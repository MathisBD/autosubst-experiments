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
  T_var : nat -> term
| (** Non-variable expr constructor, applied to a list of arguments. *)
  T_ctor : forall c, args (ctor_type S.t c) -> term
| (** Empty argument list. *)
  T_al_nil : args []
| (** Non-empty argument list. *)
  T_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)
| (** Base argument (e.g. bool or string). *)
  T_abase : forall b, denote_base S.t b -> arg (AT_base b)
| (** Term argument. *)
  T_aterm : term -> arg AT_term
| (** Binder argument. *)
  T_abind {ty} : arg ty -> arg (AT_bind ty)
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
rename (T_var i) r := T_var (r i) ;
rename (T_ctor c al) r := T_ctor c (rename al r) ;
rename T_al_nil r := T_al_nil ;
rename (T_al_cons a al) r := T_al_cons (rename a r) (rename al r) ;
rename (T_abase b x) r := T_abase b x ;
rename (T_aterm t) r := T_aterm (rename t r) ;
rename (T_abind a) r := T_abind (rename a (up_ren r)).

(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [nat -> term] which is applied 
    to all free variables. *)
Definition subst := nat -> term.

(** The identity substitution. *)
Definition sid : subst := fun i => T_var i.

(** [sshift k] shifts indices by [k]. *)
Definition sshift (k : nat) : subst := 
  fun i => T_var (k + i).

(** Cons a expr with a substitution. *)
Equations scons (t : term) (s : subst) : subst :=
scons t s 0 := t ;
scons t s (S i) := s i.

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  scons (T_var 0) (fun i => rename (s i) (rshift 1)).

(** Apply a substitution to a expr. *)
Equations substitute {k} (t : expr k) (s : subst) : expr k :=
substitute (T_var i) s := s i ;
substitute (T_ctor c al) s := T_ctor c (substitute al s) ;
substitute T_al_nil s := T_al_nil ;
substitute (T_al_cons a al) s := T_al_cons (substitute a s) (substitute al s) ;
substitute (T_abase b x) s := T_abase b x ;
substitute (T_aterm t) s := T_aterm (substitute t s) ;
substitute (T_abind a) s := T_abind (substitute a (up_subst s)).

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
Proof. 
intros i1 i2 it s1 s2 Hs i. dependent elimination i ; simp rcons.
now rewrite Hs. 
Qed.

#[global] Instance rcomp_proper n m o : Proper (point_eq ==> point_eq ==> point_eq) (@rcomp n m o).
Proof. 
intros s1 s2 Hs r1 r2 Hr i. dependent elimination i ; simp rcomp.
- now rewrite Hs, Hr.
- now rewrite Hs, Hr.
Qed.

#[global] Instance rename_proper n m k :
  Proper (eq ==> point_eq ==> eq) (@rename n m k).
Proof.
intros t _ <- r1 r2 Hr. funelim (rename t _) ; simp rename in * ; auto.
f_equal. apply H. now rewrite Hr.
Qed.

#[global] Instance up_subst_proper n m : Proper (point_eq ==> point_eq) (@up_subst n m).
Proof.
intros s1 s2 Hs i. dependent elimination i ; simp up_subst scons.
- reflexivity.
- now rewrite Hs.
Qed. 

#[global] Instance scons_proper n m : Proper (eq ==> point_eq ==> point_eq) (@scons n m).
Proof. 
intros t1 t2 Ht s1 s2 Hs i. 
dependent elimination i ; simp scons. now rewrite Hs. 
Qed.
    
#[global] Instance substitute_proper n m k : 
  Proper (eq ==> point_eq ==> eq) (@substitute n m k).
Proof. 
intros t ? <- s1 s2 Hs. funelim (substitute t _) ; simp substitute in * ; auto.
f_equal. apply H. now rewrite Hs.
Qed. 

#[global] Instance scomp_proper n m o : Proper (point_eq ==> point_eq ==> point_eq) (@scomp n m o).
Proof. 
intros s1 s2 Hs r1 r2 Hr i. dependent elimination i ; simp scomp.
- now rewrite Hs, Hr.
- now rewrite Hs, Hr.
Qed.

(*********************************************************************************)
(** *** Properties of substitution. *)
(*********************************************************************************)

Lemma up_ren_comp {n m o} (r1 : ren n m) (r2 : ren m o) : 
  rcomp (up_ren r1) (up_ren r2) =₁ up_ren (rcomp r1 r2).
Proof. intros i. dependent elimination i ; reflexivity. Qed.  

Lemma ren_ren {n m o k} (t : expr k n) (r1 : ren n m) (r2 : ren m o) : 
  rename (rename t r1) r2 = rename t (rcomp r1 r2).
Proof.
funelim (rename t _) ; simp rename in * ; auto.
now rewrite H, up_ren_comp.
Qed.

Lemma subst_ren {n m o k} (t : expr k n) (s : subst n m) (r : ren m o) : 
  rename (substitute t s) r = substitute t (fun i => rename (s i) r).
Proof.
funelim (substitute t _) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros i. dependent elimination i ; simp up_subst scons rename ; auto.
rewrite ren_ren, ren_ren. apply rename_proper ; auto.
reflexivity.
Qed.

Lemma ren_subst {n m o k} (t : expr k n) (r : ren n m) (s : subst m o) : 
  substitute (rename t r) s = substitute t (fun i => s (r i)).
Proof.
funelim (rename t r) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros i. dependent elimination i ; reflexivity.
Qed.

Lemma up_subst_comp {n m o} (s1 : subst n m) (s2 : subst m o) : 
  scomp (up_subst s1) (up_subst s2) =₁ up_subst (scomp s1 s2).
Proof. 
intros i. dependent elimination i ; simp up_subst scomp scons substitute ; auto.
rewrite ren_subst, subst_ren. apply substitute_proper ; auto.
intros i. simp scons rshift fin_weaken. reflexivity.
Qed.

Lemma subst_subst {n m o k} (t : expr k n) (s1 : subst n m) (s2 : subst m o) : 
  substitute (substitute t s1) s2 = substitute t (scomp s1 s2).
Proof.
funelim (substitute t _) ; simp substitute in * ; auto.
f_equal. rewrite H. now rewrite up_subst_comp.
Qed.

Lemma up_subst_sid : (up_subst (@sid n)) =₁ sid.
Proof. intros i ; dependent elimination i ; reflexivity. Qed.
#[global] Hint Rewrite @up_subst_sid : up_subst.

Lemma subst_sid {n k} (t : expr n k) : substitute t sid = t.
Proof.
induction t ; simp substitute in * ; auto.
rewrite up_subst_sid. auto.
Qed.
#[global] Hint Rewrite @subst_sid : substitute.

Lemma scomp_id_l (s : subst n m) : scomp sid s =₁ s.
Proof. reflexivity. Qed.
#[global] Hint Rewrite @scomp_id_l : scomp.

Lemma scomp_id_r (s : subst n m) : scomp s sid =₁ s.
Proof. intros i. simp scomp substitute. reflexivity. Qed.
#[global] Hint Rewrite @scomp_id_r : scomp.

Lemma scomp_assoc {n m o p} (s1 : subst n m) (s2 : subst m o) (s3 : subst o p) : 
  scomp (scomp s1 s2) s3 =₁ scomp s1 (scomp s2 s3).
Proof. intros i. simp scomp. now rewrite subst_subst. Qed.

Lemma ren_is_subst {n m k} (t : expr k n) (r : ren n m) : 
  rename t r = substitute t (fun i => T_var (r i)).
Proof.
funelim (rename t r) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros i. dependent elimination i ; reflexivity.
Qed.

Lemma rshift_sshift {n k} (t : expr k n) : 
  rename t (rshift 1) = substitute t (sshift 1).
Proof. rewrite ren_is_subst. reflexivity. Qed.
    
Lemma up_subst_alt (s : subst n m) :
  up_subst s =₁ scons (T_var fin_zero) (scomp s (sshift 1)).
Proof.
simp up_subst. apply scons_proper ; auto.
intros i. simp scomp. now rewrite rshift_sshift.
Qed.

Lemma sshift_succ_r k : sshift (S k) =₁ scomp (@sshift n k) (sshift 1).
Proof. intros i. dependent elimination i ; reflexivity. Qed.    

Lemma sid_scons : scons (T_var fin_zero) (sshift 1) =₁ @sid (S n).
Proof. intros i. dependent elimination i ; reflexivity. Qed.
#[global] Hint Rewrite @sid_scons : scons.

Lemma scomp_scons_distrib {n m o} (t : term m) (s1 : subst n m) (s2 : subst m o) :
  scomp (scons t s1) s2 =₁ scons (substitute t s2) (scomp s1 s2).
Proof. intros i. dependent elimination i ; reflexivity. Qed.

End Make.