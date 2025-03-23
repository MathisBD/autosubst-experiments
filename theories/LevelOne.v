From Prototype Require Import Prelude Sig.

(** This file defines terms and substitutions over an abstract signature.
    Substitutions are represented as functions [nat -> term],
    and we prove the main properties of substitution. *)

Section WithSig.
Context {sig : signature}.
Definition arg_ty := @arg_ty (base sig).

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
    Terms are indexed by a scope (a natural) and a kind. *)
Inductive term : nat -> kind -> Type :=
| (** Term variable. *)
  T_var {n} : fin n -> term n K_t
| (** Non-variable term constructor, applied to a list of arguments. *)
  T_ctor {n} : forall c, term n (K_al (ctor_type sig c)) -> term n K_t
| (** Empty argument list. *)
  T_al_nil {n} : term n (K_al [])
| (** Non-empty argument list. *)
  T_al_cons {n ty tys} : term n (K_a ty) -> term n (K_al tys) -> term n (K_al (ty :: tys))
| (** Base argument (e.g. bool or string). *)
  T_abase {n} : forall b, denote_base sig b -> term n (K_a (AT_base b))
| (** Term argument. *)
  T_aterm {n} : term n K_t -> term n (K_a AT_term)
| (** Binder argument. *)
  T_abind {n ty} : term (S n) (K_a ty) -> term n (K_a (AT_bind ty)).

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
Fixpoint rename {n m} {k} (t : term n k) (r : ren n m) : term m k :=
  match t, r with 
  | T_var i, r => T_var (r i)
  | T_ctor c args, r => T_ctor c (rename args r)
  | T_al_nil, r => T_al_nil
  | T_al_cons a args, r => T_al_cons (rename a r) (rename args r)
  | T_abase b x, r => T_abase b x
  | T_aterm t, r => T_aterm (rename t r)
  | T_abind a, r => T_abind (rename a (up_ren r))
  end.
#[global] Instance rename_notation n m k : Subst (term n k) (ren n m) (term m k) :=
{ gen_subst := rename }.
  
(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [fin n -> term m K_t] which is applied 
    to all free variables. *)
Definition subst n m := fin n -> term m K_t.

(** The identity substitution. *)
Definition sid {n} : subst n n := 
  fun i => T_var i.

(** [sshift k] shifts indices by [k]. *)
Definition sshift {n} (k : nat) : subst n (k + n) := 
  fun i => T_var (fin_weaken k i).

(** Cons a term with a substitution. *)
Definition scons {n m} (t : term m K_t) (s : subst n m) : subst (S n) m :=
  fun i => 
    match i in fin (S n0) return subst n0 m -> term m K_t with 
    | fin_zero => fun _ => t
    | fin_succ i => fun s => s i
    end s.
#[global] Instance scons_notation n m : Scons (term m K_t) (subst n m) (subst (S n) m) :=
{ gen_scons := scons }.

(** Lift a substitution through a binder. *)
Definition up_subst {n m} (s : subst n m) : subst (S n) (S m) :=
  T_var fin_zero .: (fun i => (s i)[: rshift 1]).

(** Apply a substitution to a term. *)
Fixpoint substitute {n m} {k} (t : term n k) (s : subst n m) : term m k :=
  match t, s with 
  | T_var n, s => s n
  | T_ctor c args, s => T_ctor c (substitute args s)
  | T_al_nil, s => T_al_nil
  | T_al_cons a args, s => T_al_cons (substitute a s) (substitute args s)
  | T_abase b x, s => T_abase b x
  | T_aterm t, s => T_aterm (substitute t s)
  | T_abind a, s => T_abind (substitute a (up_subst s))
  end.
#[global] Instance substitute_notation n m k : Subst (term n k) (subst n m) (term m k) :=
{ gen_subst := substitute }.

(** Left to right composition of substitutions. *)
Definition scomp {n m o} (s1 : subst n m) (s2 : subst m o) : subst n o :=
  fun i => (s1 i)[: s2].
#[global] Instance scomp_notation n m o : Scomp (subst n m) (subst m o) (subst n o) :=
{ gen_scomp := scomp }.

(*********************************************************************************)
(** *** Setoid Rewrite Support. *)
(*********************************************************************************)

(** Pointwise equality for functions. *)
Definition point_eq {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (point_eq f g) (at level 75).

#[global] Instance up_ren_proper n m : Proper (point_eq ==> point_eq) (@up_ren n m).
Proof. 
intros r1 r2 Hr i. dependent destruction i ; cbv [up_ren] ; simpl.
- reflexivity.
- cbv [rcomp rshift]. auto.
Qed. 

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

#[global] Instance substitute_proper n m k : 
  Proper (eq ==> point_eq ==> eq) (@substitute n m k).
Proof. 
intros t ? <-. revert m. induction t ; intros m s1 s2 Hs ; simpl ; try (now auto).
- specialize (IHt m). auto.
- specialize (IHt1 m). specialize (IHt2 m). auto.
- specialize (IHt m). auto.
- f_equal. apply IHt. now rewrite Hs.
Qed. 

(*********************************************************************************)
(** *** Properties of substitution. *)
(*********************************************************************************)

(*Lemma rshift1 n (i : fin n) : rshift 1 i = fin_succ i.
Proof. cbv [rshift]. simpl. reflexivity. Qed.*)

Lemma up_ren_comp {n m o} (r1 : ren n m) (r2 : ren m o) : 
  up_ren r1 >> up_ren r2 =₁ up_ren (r1 >> r2).
Proof. intros i. dependent destruction i ; reflexivity. Qed.

Lemma ren_ren {n m o k} (t : term n k) (r1 : ren n m) (r2 : ren m o) : 
  t[: r1][: r2] = t[: r1 >> r2].
Proof.
revert m o r1 r2. induction t ; intros m o r1 r2 ; simpl ; try (now auto).
- now setoid_rewrite IHt.
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- setoid_rewrite IHt. now rewrite up_ren_comp.
Qed.

Lemma subst_ren {n m o k} (t : term n k) (s : subst n m) (r : ren m o) : 
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

Lemma ren_subst {n m o k} (t : term n k) (r : ren n m) (s : subst m o) : 
  t[: r][: s] = t[: fun n => s (r n)].
Proof.
revert m o s r. induction t ; intros m o s r ; simpl ; try (now auto).
- now setoid_rewrite IHt. 
- setoid_rewrite IHt1. now setoid_rewrite IHt2.
- now setoid_rewrite IHt.
- f_equal. setoid_rewrite IHt. apply substitute_proper ; [reflexivity|].
  intros i ; dependent destruction i ; reflexivity.
Qed.  

Lemma subst_subst {n m o k} (t : term n k) (s1 : subst n m) (s2 : subst m o) : 
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

End WithSig.