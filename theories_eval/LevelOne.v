From Prototype Require Import Prelude Sig.

(** This file defines exprs and substitutions over an abstract signature.
    Substitutions are represented as functions [nat -> term],
    and we prove the main properties of substitution. *)

Module Make (S : Sig).

(*********************************************************************************)
(** *** Terms. *)
(*********************************************************************************)

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

(** [rshift] shifts indices by one. *)
Definition rshift : ren := fun i => S i.

(** Cons an index with a renaming. *)
Equations rcons (i0 : nat) (r : ren) : ren :=
rcons i0 _ 0 := i0 ;
rcons i0 r (S i) := r i.

(** Compose two renamings (left to right composition). *)
Definition rcomp (r1 r2 : ren) : ren :=
  fun i => r2 (r1 i).

(** Lift a renaming through a binder. *)
Definition up_ren (r : ren) : ren := 
  rcons 0 (rcomp r rshift).
 
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

(** [sshift] shifts indices by one. *)
Definition sshift : subst := 
  fun i => E_var (S i).

(** Cons a expr with a substitution. *)
Equations scons (t : term) (s : subst) : subst :=
scons t s 0 := t ;
scons t s (S i) := s i.

(** Left to right composition of a substitution with a renaming. *)
Definition srcomp (s : subst) (r : ren) := 
  fun i => rename (s i) r.

(** Left to right composition of a renaming with a substitution. *)
Definition rscomp (r : ren) (s : subst) := 
  fun i => s (r i).

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  scons (E_var 0) (srcomp s rshift).

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

#[global] Instance rscomp_proper : Proper (point_eq ==> point_eq ==> point_eq) rscomp.
Proof. intros r1 r2 Hr s1 s2 Hs i. cbv [rscomp]. now rewrite Hs, Hr. Qed.

#[global] Instance srcomp_proper : Proper (point_eq ==> point_eq ==> point_eq) srcomp.
Proof. intros s1 s2 Hs r1 r2 Hr i. cbv [srcomp]. now rewrite Hs, Hr. Qed.

#[global] Instance scons_proper : Proper (eq ==> point_eq ==> point_eq) scons.
Proof. 
intros t1 t2 Ht s1 s2 Hs i. 
destruct i ; simp scons. now rewrite Hs. 
Qed.

#[global] Instance up_subst_proper : Proper (point_eq ==> point_eq) up_subst.
Proof. intros s1 s2 Hs. cbv [up_subst]. now rewrite Hs. Qed.

#[global] Instance substitute_proper k : 
  Proper (eq ==> point_eq ==> eq) (@substitute k).
Proof. 
intros t ? <- s1 s2 Hs. funelim (substitute t _) ; simp substitute in * ; auto.
f_equal. apply H. now rewrite Hs.
Qed. 

#[global] Instance scomp_proper : Proper (point_eq ==> point_eq ==> point_eq) scomp.
Proof. intros s1 s2 Hs r1 r2 Hr i. cbv [scomp]. now rewrite Hs, Hr. Qed.

(*********************************************************************************)
(** *** Properties of renaming and substitution. *)
(*********************************************************************************)

(*Lemma rshift_plus k l : rcomp (rshift k) (rshift l) =₁ rshift (k + l).
Proof. intros i. cbv [rcomp rshift]. lia. Qed.

Lemma rshift_succ_l k : rcomp (rshift 1) (rshift k) =₁ rshift (S k).
Proof. rewrite rshift_plus. reflexivity. Qed.
    
Lemma rshift_succ_r k : rcomp (rshift k) (rshift 1) =₁ rshift (S k).
Proof. rewrite rshift_plus. intros i. cbv [rshift]. lia. Qed.

Lemma sshift_plus k l : scomp (sshift k) (sshift l) =₁ sshift (k + l).
Proof. 
induction k as [|k IH] ; intros i ; cbv [scomp sshift substitute] ; simpl.
- reflexivity.
- f_equal. lia.
Qed.   

Lemma sshift_succ_l k : scomp (sshift 1) (sshift k) =₁ sshift (S k).
Proof. rewrite sshift_plus. reflexivity. Qed.
    
Lemma sshift_succ_r k : scomp (sshift k) (sshift 1) =₁ sshift (S k).
Proof. rewrite sshift_plus. intros i. cbv [sshift]. f_equal ; lia. Qed.*)

Lemma rid_rcons : rcons 0 rshift =₁ rid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma sid_scons : scons (E_var 0) sshift =₁ sid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma rcomp_rcons_distrib i (r1 r2 : ren) :
  rcomp (rcons i r1) r2 =₁ rcons (r2 i) (rcomp r1 r2).
Proof. intros [|i'] ; reflexivity. Qed.

Lemma scomp_scons_distrib (t : term) (s1 s2 : subst) :
  scomp (scons t s1) s2 =₁ scons (substitute t s2) (scomp s1 s2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma rshift_rcons i (r : ren) : rcomp rshift (rcons i r) =₁ r.
Proof. reflexivity. Qed.
    
Lemma sshift_scons (t : term) (s : subst) : scomp sshift (scons t s) =₁ s.
Proof. reflexivity. Qed.

Lemma rcomp_rid_l (r : ren) : rcomp rid r =₁ r.
Proof. reflexivity. Qed.

Lemma rcomp_rid_r (r : ren) : rcomp r rid =₁ r.
Proof. reflexivity. Qed.

Lemma rcomp_assoc (r1 r2 r3 : ren) : 
  rcomp (rcomp r1 r2) r3 =₁ rcomp r1 (rcomp r2 r3).
Proof. reflexivity. Qed.

Lemma up_ren_rid : up_ren rid =₁ rid.
Proof. intros [|] ; reflexivity. Qed.

Lemma up_ren_comp (r1 r2 : ren) : 
  rcomp (up_ren r1) (up_ren r2) =₁ up_ren (rcomp r1 r2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma ren_rid {k} (t : expr k) : rename t rid = t.
Proof. induction t ; simp rename ; triv. now rewrite up_ren_rid, IHt. Qed.

Lemma ren_ren {k} (t : expr k) (r1 r2 : ren) : 
  rename (rename t r1) r2 = rename t (rcomp r1 r2).
Proof.
funelim (rename t _) ; simp rename in * ; auto.
now rewrite H, up_ren_comp.
Qed.

Lemma ren_subst {k} (t : expr k) (s : subst) (r : ren) : 
  rename (substitute t s) r = substitute t (srcomp s r).
Proof.
funelim (substitute t _) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; auto. cbv [up_subst scons srcomp].
rewrite ren_ren, ren_ren. apply rename_proper ; auto.
reflexivity.
Qed.

Lemma subst_ren {k} (t : expr k) (r : ren) (s : subst) : 
  substitute (rename t r) s = substitute t (rscomp r s).
Proof.
funelim (rename t r) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; reflexivity.
Qed.

Lemma up_subst_comp (s1 s2 : subst) : 
  scomp (up_subst s1) (up_subst s2) =₁ up_subst (scomp s1 s2).
Proof. 
intros [|i] ; auto. cbv [up_subst scomp]. simp scons. cbv [srcomp].
rewrite ren_subst, subst_ren. now apply substitute_proper.
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

Lemma scomp_sid_l (s : subst) : scomp sid s =₁ s.
Proof. reflexivity. Qed.

Lemma scomp_sid_r (s : subst) : scomp s sid =₁ s.
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
  rename t rshift = substitute t sshift.
Proof. rewrite ren_is_subst. reflexivity. Qed.
    
Lemma up_subst_alt (s : subst) :
  up_subst s =₁ scons (E_var 0) (scomp s sshift).
Proof.
simp up_subst. apply scons_proper ; auto.
intros i. cbv [scomp srcomp]. now rewrite rshift_sshift.
Qed.

End Make.