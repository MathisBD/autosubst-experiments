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
Definition rid {n} : ren n n := 
  fun i => i.

(** [rshift k] shifts indices by [k]. *)
Definition rshift {n} (k : nat) : ren n (k + n) := 
  fun i => fin_weaken k i.

(** Cons an index with a renaming. *)
Definition rcons {n m} (i0 : fin m) (r : ren n m) : ren (S n) m :=
  fun i =>
    match i in fin (S n0) return ren n0 m -> fin m with 
    | fin_zero => fun _ => i0
    | fin_succ i => fun r => r i
    end r.
#[global] Instance rcons_notation n m : Scons (fin m) (ren n m) (ren (S n) m) :=
{ gen_scons := @rcons n m }.

(** Compose two renamings (left to right composition). *)
Definition rcomp {n m o} (r1 : ren n m) (r2 : ren m o) : ren n o :=
  fun i => r2 (r1 i).
#[global] Instance rcomp_notation {n m o} : Scomp (ren n m) (ren m o) (ren n o) :=
{ gen_scomp := rcomp }.

(** Lift a renaming through a binder. *)
Definition up_ren {n m} (r : ren n m) : ren (S n) (S m) := 
  fin_zero .: r >> rshift 1.
 
(** Rename a term. *)
Fixpoint rename {n m} {k} (t : term k n) (r : ren n m) : term k m :=
  match t, r with 
  | T_var i, r => T_var (r i)
  | T_ctor c args, r => T_ctor c (rename args r)
  | T_al_nil, r => T_al_nil
  | T_al_cons a args, r => T_al_cons (rename a r) (rename args r)
  | T_abase b x, r => T_abase b x
  | T_aterm t, r => T_aterm (rename t r)
  | T_abind a, r => T_abind (rename a (up_ren r))
  end.
#[global] Instance rename_notation n m k : Subst (term k n) (ren n m) (term k m) :=
{ gen_subst := rename }.
  
(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [fin n -> term K_t m] which is applied 
    to all free variables. *)
Definition subst n m := fin n -> term K_t m.

(** The identity substitution. *)
Definition sid {n} : subst n n := 
  fun i => T_var i.

(** [sshift k] shifts indices by [k]. *)
Definition sshift {n} (k : nat) : subst n (k + n) := 
  fun i => T_var (fin_weaken k i).

(** Cons a term with a substitution. *)
Definition scons {n m} (t : term K_t m) (s : subst n m) : subst (S n) m :=
  fun i => 
    match i in fin (S n0) return subst n0 m -> term K_t m with 
    | fin_zero => fun _ => t
    | fin_succ i => fun s => s i
    end s.
#[global] Instance scons_notation n m : Scons (term K_t m) (subst n m) (subst (S n) m) :=
{ gen_scons := scons }.

(** Lift a substitution through a binder. *)
Definition up_subst {n m} (s : subst n m) : subst (S n) (S m) :=
  T_var fin_zero .: (fun i => (s i)[: rshift 1]).

(** Apply a substitution to a term. *)
Fixpoint substitute {n m} {k} (t : term k n) (s : subst n m) : term k m :=
  match t, s with 
  | T_var n, s => s n
  | T_ctor c args, s => T_ctor c (substitute args s)
  | T_al_nil, s => T_al_nil
  | T_al_cons a args, s => T_al_cons (substitute a s) (substitute args s)
  | T_abase b x, s => T_abase b x
  | T_aterm t, s => T_aterm (substitute t s)
  | T_abind a, s => T_abind (substitute a (up_subst s))
  end.
#[global] Instance substitute_notation n m k : Subst (term k n) (subst n m) (term k m) :=
{ gen_subst := substitute }.

(** Left to right composition of substitutions. *)
Definition scomp {n m o} (s1 : subst n m) (s2 : subst m o) : subst n o :=
  fun i => (s1 i)[: s2].
#[global] Instance scomp_notation n m o : Scomp (subst n m) (subst m o) (subst n o) :=
{ gen_scomp := scomp }.

(*********************************************************************************)
(** *** Setoid Rewrite Support. *)
(*********************************************************************************)

#[global] Instance up_ren_proper n m : Proper (point_eq ==> point_eq) (@up_ren n m).
Proof. 
intros r1 r2 Hr i. dependent destruction i ; cbv [up_ren] ; simpl.
- reflexivity.
- cbv [rcomp rshift]. auto.
Qed. 

#[global] Instance rcons_proper n m : Proper (eq ==> point_eq ==> point_eq) (@rcons n m).
Proof. intros i1 i2 it s1 s2 Hs i. dependent destruction i ; auto. Qed.

#[global] Instance rcomp_proper n m o : Proper (point_eq ==> point_eq ==> point_eq) (@rcomp n m o).
Proof. intros s1 s2 Hs r1 r2 Hr i. dependent destruction i ; cbv [rcomp] ; auto. Qed.

#[global] Instance rename_proper n m k :
  Proper (eq ==> point_eq ==> eq) (@rename n m k).
Proof.
intros t ? <-. revert m. 
induction t ; intros m s1 s2 Hs ; simpl ; try (now auto).
- specialize (IHt m). auto.
- specialize (IHt1 m). specialize (IHt2 m). auto.
- specialize (IHt m). auto.
- f_equal. apply IHt. now rewrite Hs.
Qed.

#[global] Instance up_subst_proper n m : Proper (point_eq ==> point_eq) (@up_subst n m).
Proof.
intros s1 s2 Hs i. dependent destruction i ; cbv [up_subst] ; simpl.
- reflexivity.
- now rewrite Hs.
Qed. 

#[global] Instance scons_proper n m : Proper (eq ==> point_eq ==> point_eq) (@scons n m).
Proof. intros t1 t2 Ht s1 s2 Hs i. dependent destruction i ; auto. Qed.
    
#[global] Instance substitute_proper n m k : 
  Proper (eq ==> point_eq ==> eq) (@substitute n m k).
Proof. 
intros t ? <-. revert m. induction t ; intros m s1 s2 Hs ; simpl ; try (now auto).
- specialize (IHt m). auto.
- specialize (IHt1 m). specialize (IHt2 m). auto.
- specialize (IHt m). auto.
- f_equal. apply IHt. now rewrite Hs.
Qed. 

#[global] Instance scomp_proper n m o : Proper (point_eq ==> point_eq ==> point_eq) (@scomp n m o).
Proof. 
intros s1 s2 Hs r1 r2 Hr i. 
dependent destruction i ; cbv [scomp] ; simpl ; setoid_rewrite Hs ; setoid_rewrite Hr ; reflexivity.
Qed.

(*********************************************************************************)
(** *** Properties of substitution. *)
(*********************************************************************************)

Lemma up_ren_comp {n m o} (r1 : ren n m) (r2 : ren m o) : 
  up_ren r1 >> up_ren r2 =₁ up_ren (r1 >> r2).
Proof. intros i. dependent destruction i ; reflexivity. Qed.

Lemma ren_ren {n m o k} (t : term k n) (r1 : ren n m) (r2 : ren m o) : 
  t[: r1][: r2] = t[: r1 >> r2].
Proof.
revert m o r1 r2. induction t ; intros m o r1 r2 ; simpl ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- setoid_rewrite IHt. now rewrite up_ren_comp.
Qed.

Lemma subst_ren {n m o k} (t : term k n) (s : subst n m) (r : ren m o) : 
  t[: s][: r] = t[: fun n => (s n)[: r]].
Proof.
revert m o s r. induction t ; intros m o s r ; simpl ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [reflexivity|].
  intros i ; dependent destruction i ; simpl ; [reflexivity|].
  cbv [up_subst]. simpl. repeat setoid_rewrite ren_ren.
  apply rename_proper ; reflexivity.
Qed.

Lemma ren_subst {n m o k} (t : term k n) (r : ren n m) (s : subst m o) : 
  t[: r][: s] = t[: fun n => s (r n)].
Proof.
revert m o s r. induction t ; intros m o s r ; simpl ; try (now auto).
- now setoid_rewrite IHt. 
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [reflexivity|].
  intros i ; dependent destruction i ; reflexivity.
Qed.  

Lemma subst_subst {n m o k} (t : term k n) (s1 : subst n m) (s2 : subst m o) : 
  t[: s1][: s2] = t[: s1 >> s2].
Proof.
revert m o s1 s2. induction t ; intros m o s1 s2 ; cbn ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. setoid_rewrite IHt2. reflexivity.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [reflexivity | simpl].
  intros i ; dependent destruction i ; simpl ; [reflexivity|].
  cbv [scomp]. simpl. setoid_rewrite subst_ren. setoid_rewrite ren_subst. reflexivity.
Qed.

Lemma up_subst_sid {n} : (up_subst (@sid n)) =₁ sid.
Proof. intros i ; dependent destruction i ; reflexivity. Qed.

Lemma subst_sid {n k} (t : term n k) : t[: sid] = t.
Proof.
induction t ; try (now auto).
simpl. rewrite up_subst_sid. now setoid_rewrite IHt.
Qed.

Lemma scomp_id_l {n m} (s : subst n m) : sid >> s =₁ s.
Proof. reflexivity. Qed.

Lemma scomp_id_r {n m} (s : subst n m) : s >> sid =₁ s.
Proof. intros i. simpl. cbv [scomp]. now setoid_rewrite subst_sid. Qed.    

Lemma scomp_assoc {n m o p} (s1 : subst n m) (s2 : subst m o) (s3 : subst o p) : 
  (s1 >> s2) >> s3 =₁ s1 >> (s2 >> s3).
Proof. intros i. simpl. cbv [scomp]. now setoid_rewrite subst_subst. Qed.

Lemma ren_is_subst {n m k} (t : term k n) (r : ren n m) : 
    t[: r] = t[: fun i => T_var (r i)].
Proof.
revert m r. dependent induction t ; simpl ; intros m r ; try auto. 
- setoid_rewrite IHt. reflexivity.
- setoid_rewrite IHt1. setoid_rewrite IHt2. reflexivity.
- setoid_rewrite IHt. reflexivity.
- setoid_rewrite IHt. f_equal. apply substitute_proper ; auto.
  intros i. dependent destruction i ; reflexivity.
Qed.

Lemma rshift_sshift {n k} (t : term k n) : t[: rshift 1] = t[: sshift 1].
Proof. rewrite ren_is_subst. reflexivity. Qed.
    
Lemma up_subst_alt {n m} (s : subst n m) :
  up_subst s =₁ T_var fin_zero .: (s >> sshift 1).
Proof.
unfold up_subst. apply scons_proper ; auto.
intros i. simpl. cbv [scomp]. now setoid_rewrite rshift_sshift.
Qed.

Lemma sshift_succ_r {n} k : sshift (S k) =₁ @sshift n k >> sshift 1.
Proof. intros i. dependent destruction i ; reflexivity. Qed.    

Lemma sid_scons {n} : T_var fin_zero .: sshift 1 =₁ @sid (S n).
Proof. intros i. dependent destruction i ; reflexivity. Qed.

Lemma scomp_scons_distrib {n m o} (t : term K_t m) (s1 : subst n m) (s2 : subst m o) :
  (t .: s1) >> s2 =₁ t[: s2 ] .: s1 >> s2.
Proof. intros i. dependent destruction i ; reflexivity. Qed.

End Make.