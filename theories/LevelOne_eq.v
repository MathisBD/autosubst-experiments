From Prototype Require Import Prelude Sig.

(** This file defines terms and substitutions over an abstract signature.
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
  K_t : kind
| (** Constructor argument. *)
  K_a : arg_ty -> kind
| (** List of constructor arguments. *)
  K_al : list arg_ty -> kind.

(** Terms over an abstract signature. 
    Terms are indexed by a kind and a scope (a natural). *)
Inductive term : kind -> nat -> Type :=
| (** Term variable. *)
  T_var {n} : fin n -> term K_t n
| (** Non-variable term constructor, applied to a list of arguments. *)
  T_ctor {n} : forall c, term (K_al (ctor_type S.t c)) n -> term K_t n
| (** Empty argument list. *)
  T_al_nil {n} : term (K_al []) n
| (** Non-empty argument list. *)
  T_al_cons {n ty tys} : term (K_a ty) n -> term (K_al tys) n -> term (K_al (ty :: tys)) n
| (** Base argument (e.g. bool or string). *)
  T_abase {n} : forall b, denote_base S.t b -> term (K_a (AT_base b)) n
| (** Term argument. *)
  T_aterm {n} : term K_t n -> term (K_a AT_term) n
| (** Binder argument. *)
  T_abind {n ty} : term (K_a ty) (S n) -> term (K_a (AT_bind ty)) n.

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** A renaming on terms is a function [fin n -> fin m] which is applied
    to all free variables. *)
Definition ren n m := fin n -> fin m.

(** The identity renaming. *)
Equations rid {n} : ren n n := 
rid i := i.

(** [rshift k] shifts indices by [k]. *)
Equations rshift {n} (k : nat) : ren n (k + n) := 
rshift k i := fin_weaken k i.

(** Cons an index with a renaming. *)
Equations rcons {n m} (i0 : fin m) (r : ren n m) : ren (S n) m :=
rcons i0 _ fin_zero := i0 ;
rcons i0 r (fin_succ i) := r i.

(*#[global] Instance rcons_notation n m : Scons (fin m) (ren n m) (ren (S n) m) :=
{ gen_scons := @rcons n m }.*)

(** Compose two renamings (left to right composition). *)
Equations rcomp {n m o} (r1 : ren n m) (r2 : ren m o) : ren n o :=
rcomp r1 r2 i := r2 (r1 i).
(*#[global] Instance rcomp_notation {n m o} : Scomp (ren n m) (ren m o) (ren n o) :=
{ gen_scomp := rcomp }.*)

(** Lift a renaming through a binder. *)
Equations up_ren {n m} (r : ren n m) : ren (S n) (S m) := 
up_ren r := rcons fin_zero (rcomp r (rshift 1)).
 
(** Rename a term. *)
Equations rename {n m} {k} (t : term k n) (r : ren n m) : term k m :=
rename (T_var i) r := T_var (r i) ;
rename (T_ctor c args) r := T_ctor c (rename args r) ;
rename T_al_nil r := T_al_nil ;
rename (T_al_cons a args) r := T_al_cons (rename a r) (rename args r) ;
rename (T_abase b x) r := T_abase b x ;
rename (T_aterm t) r := T_aterm (rename t r) ;
rename (T_abind a) r := T_abind (rename a (up_ren r)).
(*#[global] Instance rename_notation n m k : Subst (term k n) (ren n m) (term k m) :=
{ gen_subst := rename }.*)
  
(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [fin n -> term K_t m] which is applied 
    to all free variables. *)
Definition subst n m := fin n -> term K_t m.

(** The identity substitution. *)
Equations sid {n} : subst n n := 
sid i := T_var i.

(** [sshift k] shifts indices by [k]. *)
Equations sshift {n} (k : nat) : subst n (k + n) := 
sshift k i := T_var (fin_weaken k i).

(** Cons a term with a substitution. *)
Equations scons {n m} (t : term K_t m) (s : subst n m) : subst (S n) m :=
scons t s fin_zero := t ;
scons t s (fin_succ i) := s i.
(*#[global] Instance scons_notation n m : Scons (term K_t m) (subst n m) (subst (S n) m) :=
{ gen_scons := scons }.*)

(** Lift a substitution through a binder. *)
Equations up_subst {n m} (s : subst n m) : subst (S n) (S m) :=
up_subst s := scons (T_var fin_zero) (fun i => rename (s i) (rshift 1)).

(** Apply a substitution to a term. *)
Equations substitute {n m} {k} (t : term k n) (s : subst n m) : term k m :=
substitute (T_var i) s := s i ;
substitute (T_ctor c args) s := T_ctor c (substitute args s) ;
substitute T_al_nil s := T_al_nil ;
substitute (T_al_cons a args) s := T_al_cons (substitute a s) (substitute args s) ;
substitute (T_abase b x) s := T_abase b x ;
substitute (T_aterm t) s := T_aterm (substitute t s) ;
substitute (T_abind a) s := T_abind (substitute a (up_subst s)).
(*#[global] Instance substitute_notation n m k : Subst (term k n) (subst n m) (term k m) :=
{ gen_subst := substitute }.*)

(** Left to right composition of substitutions. *)
Equations scomp {n m o} (s1 : subst n m) (s2 : subst m o) : subst n o :=
scomp s1 s2 i := substitute (s1 i) s2.
(*#[global] Instance scomp_notation n m o : Scomp (subst n m) (subst m o) (subst n o) :=
{ gen_scomp := scomp }.*)

(*********************************************************************************)
(** *** Setoid Rewrite Support. *)
(*********************************************************************************)

#[global] Instance up_ren_proper n m : Proper (point_eq ==> point_eq) (@up_ren n m).
Proof. 
intros r1 r2 Hr i. dependent elimination i ; simp up_ren rcons rcomp.
- reflexivity.
- now rewrite Hr.
Qed. 

#[global] Instance rcons_proper n m : Proper (eq ==> point_eq ==> point_eq) (@rcons n m).
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

Lemma ren_ren {n m o k} (t : term k n) (r1 : ren n m) (r2 : ren m o) : 
  rename (rename t r1) r2 = rename t (rcomp r1 r2).
Proof.
funelim (rename t _) ; simp rename in * ; auto.
now rewrite H, up_ren_comp.
Qed.

Lemma subst_ren {n m o k} (t : term k n) (s : subst n m) (r : ren m o) : 
  rename (substitute t s) r = substitute t (fun i => rename (s i) r).
Proof.
funelim (substitute t _) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros i. dependent elimination i ; simp up_subst scons rename ; auto.
rewrite ren_ren, ren_ren. apply rename_proper ; auto.
reflexivity.
Qed.

Lemma ren_subst {n m o k} (t : term k n) (r : ren n m) (s : subst m o) : 
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

Lemma subst_subst {n m o k} (t : term k n) (s1 : subst n m) (s2 : subst m o) : 
  substitute (substitute t s1) s2 = substitute t (scomp s1 s2).
Proof.
funelim (substitute t _) ; simp substitute in * ; auto.
f_equal. rewrite H. now rewrite up_subst_comp.
Qed.

Lemma up_subst_sid {n} : (up_subst (@sid n)) =₁ sid.
Proof. intros i ; dependent elimination i ; reflexivity. Qed.
#[global] Hint Rewrite @up_subst_sid : up_subst.

Lemma subst_sid {n k} (t : term n k) : substitute t sid = t.
Proof.
induction t ; simp substitute in * ; auto.
rewrite up_subst_sid. auto.
Qed.
#[global] Hint Rewrite @subst_sid : substitute.

Lemma scomp_id_l {n m} (s : subst n m) : scomp sid s =₁ s.
Proof. reflexivity. Qed.
#[global] Hint Rewrite @scomp_id_l : scomp.

Lemma scomp_id_r {n m} (s : subst n m) : scomp s sid =₁ s.
Proof. intros i. simp scomp substitute. reflexivity. Qed.
#[global] Hint Rewrite @scomp_id_r : scomp.

Lemma scomp_assoc {n m o p} (s1 : subst n m) (s2 : subst m o) (s3 : subst o p) : 
  scomp (scomp s1 s2) s3 =₁ scomp s1 (scomp s2 s3).
Proof. intros i. simp scomp. now rewrite subst_subst. Qed.

Lemma ren_is_subst {n m k} (t : term k n) (r : ren n m) : 
  rename t r = substitute t (fun i => T_var (r i)).
Proof.
funelim (rename t r) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros i. dependent elimination i ; reflexivity.
Qed.

Lemma rshift_sshift {n k} (t : term k n) : 
  rename t (rshift 1) = substitute t (sshift 1).
Proof. rewrite ren_is_subst. reflexivity. Qed.
    
Lemma up_subst_alt {n m} (s : subst n m) :
  up_subst s =₁ scons (T_var fin_zero) (scomp s (sshift 1)).
Proof.
simp up_subst. apply scons_proper ; auto.
intros i. simp scomp. now rewrite rshift_sshift.
Qed.

Lemma sshift_succ_r {n} k : sshift (S k) =₁ scomp (@sshift n k) (sshift 1).
Proof. intros i. dependent elimination i ; reflexivity. Qed.    

Lemma sid_scons {n} : scons (T_var fin_zero) (sshift 1) =₁ @sid (S n).
Proof. intros i. dependent elimination i ; reflexivity. Qed.
#[global] Hint Rewrite @sid_scons : scons.

Lemma scomp_scons_distrib {n m o} (t : term K_t m) (s1 : subst n m) (s2 : subst m o) :
  scomp (scons t s1) s2 =₁ scons (substitute t s2) (scomp s1 s2).
Proof. intros i. dependent elimination i ; reflexivity. Qed.

End Make.