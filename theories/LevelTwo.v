From Prototype Require Import Prelude Sig.

Module Make (S : Sig).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Terms and substitutions. *)
(*********************************************************************************)

(** Terms and substitutions are indexed by kinds. *)
Inductive kind := 
| (** Term. *)
  K_t : kind
| (** Constructor argument. *)
  K_a : arg_ty -> kind
| (** List of constructor arguments. *)
  K_al : list arg_ty -> kind
| (** Substitution. *)
  K_s : kind.  
Derive NoConfusion for kind.

(** Terms and substitutions are indexed by a scope. *)
Inductive scope :=
| (** Scope of a term, argument, or argument list. *)
  S1 : nat -> scope
| (** Scope of a substitution. *)
  S2 : nat -> nat -> scope.
Derive NoConfusion for scope.

(** A term/substitution metavariable is encoded as a unique identifier (a natural).
    When denoting a term, we have access to an environment which maps metavariable identifiers
    to actual (denoted) terms. *)
Definition mvar (k : kind) (s : scope) := nat.

(** Terms over an abstract signature. 
    Terms are indexed by a kind and a scope. *)
Inductive term : kind -> scope -> Type :=
| (** Term variable. *)
  T_var {n} : fin n -> term K_t (S1 n)
| (** Non-variable term constructor, applied to a list of arguments. *)
  T_ctor {n} : forall c, term (K_al (ctor_type S.t c)) (S1 n) -> term K_t (S1 n)
| (** Empty argument list. *)
  T_al_nil {n} : term (K_al []) (S1 n)
| (** Non-empty argument list. *)
  T_al_cons {n ty tys} : term (K_a ty) (S1 n) -> term (K_al tys) (S1 n) -> term (K_al (ty :: tys)) (S1 n)
| (** Base argument (e.g. bool or string). *)
  T_abase {n} : forall b, denote_base S.t b -> term (K_a (AT_base b)) (S1 n)
| (** Term argument. *)
  T_aterm {n} : term K_t (S1 n) -> term (K_a AT_term) (S1 n)
| (** Binder argument. *)
  T_abind {n ty} : term (K_a ty) (S1 (S n)) -> term (K_a (AT_bind ty)) (S1 n)
| (** Substitution applied to a term/argument/argument-list. *)
  T_subst {n m k} : term k (S1 n) -> term K_s (S2 n m) -> term k (S1 m)
| (** Shift substitution. *)
  T_sshift {n} : forall k, term K_s (S2 n (k + n))
| (** Cons substitution. *)
  T_scons {n m} : term K_t (S1 m) -> term K_s (S2 n m) -> term K_s (S2 (S n) m)
| (** Composition of substitutions. *)
  T_scomp {n m o} : term K_s (S2 n m) -> term K_s (S2 m o) -> term K_s (S2 n o)
| (** Metavariable. *)
  T_mvar {k s} : mvar k s -> term k s.
Derive Signature NoConfusion for term.

(** The identity substitution. *)
Definition sid {n} : term K_s (S2 n n) := T_sshift 0.

#[local] Notation "↑ k" := (T_sshift k) (at level 0).
#[local] Notation "t .: s" := (T_scons t s) (at level 60, right associativity).
#[local] Notation "s1 >> s2" := (T_scomp s1 s2) (at level 50, left associativity).
#[local] Notation "t '[:' s ']'" := (T_subst t s) (at level 15, s at level 0, no associativity).

(** Lift a substitution through a binder. *)
Equations up_subst {n m} (s : term K_s (S2 n m)) : term K_s (S2 (S n) (S m)) :=
up_subst s := T_var fin_zero .: s >> ↑1.

(*********************************************************************************)
(** *** Axiomatic equality. *)
(*********************************************************************************)

(** [t =σ t'] means that the terms/substitutions [t] and [t'] are equal 
    modulo the equational theory of sigma calculus. *)
Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
Inductive axiom_eq : forall {k s}, term k s -> term k s -> Prop :=

(** Equivalence. *)

| aeq_refl {k s} (t : term k s) : t =σ t
| aeq_sym {k s} (t1 t2 : term k s) : t1 =σ t2 -> t2 =σ t1
| aeq_trans {k s} (t1 t2 t3 : term k s) : t1 =σ t2 -> t2 =σ t3 -> t1 =σ t3

(** Congruence. *)

| aeq_congr_ctor {n} c (args1 args2 : term _ (S1 n)) : 
    args1 =σ args2 -> T_ctor c args1 =σ T_ctor c args2
| aeq_congr_al_cons {n ty tys} (a1 a2 : term (K_a ty) (S1 n)) (args1 args2 : term (K_al tys) (S1 n)) : 
    a1 =σ a2 -> args1 =σ args2 -> T_al_cons a1 args1 =σ T_al_cons a2 args2
| aeq_congr_aterm {n} (t1 t2 : term K_t (S1 n)) : 
    t1 =σ t2 -> T_aterm t1 =σ T_aterm t2
| aeq_congr_abind {n ty} (a1 a2 : term (K_a ty) (S1 (S n))) : 
    a1 =σ a2 -> T_abind a1 =σ T_abind a2
| aeq_congr_subst {n m k} (t1 t2 : term k (S1 n)) (s1 s2 : term K_s (S2 n m)) : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 
| aeq_congr_scons {n m} (t1 t2 : term K_t (S1 m)) (s1 s2 : term K_s (S2 n m)) : 
    t1 =σ t2 -> s1 =σ s2 -> t1 .: s1 =σ t2 .: s2
| aeq_congr_scomp {n m o} (s1 s2 : term K_s (S2 n m)) (r1 r2 : term K_s (S2 m o)) : 
    s1 =σ s2 -> r1 =σ r2 -> s1 >> r1 =σ s2 >> r2

(** Apply a substitution to a variable. *)

| aeq_sshift_var {n} (i : fin n) k : 
    (T_var i)[: ↑k ] =σ T_var (fin_weaken k i)
| aeq_scons_zero {n m} (t : term K_t (S1 m)) (s : term K_s (S2 n m)) :
    (T_var fin_zero)[: t .: s] =σ t
| aeq_scons_succ {n m} (i : fin n) (t : term K_t (S1 m)) (s : term K_s (S2 n m)) :
    (T_var (fin_succ i))[: t .: s] =σ (T_var i)[: s]

(** Apply a substitution to a term. *)

| aeq_subst_ctor {n m} c (args : term (K_al _) (S1 n)) (s : term K_s (S2 n m)) : 
    (T_ctor c args)[: s ] =σ T_ctor c (args[: s ])
| aeq_subst_al_nil {n m} (s : term K_s (S2 n m)) : 
    T_al_nil[: s ] =σ T_al_nil
| aeq_subst_al_cons {n m ty tys} (a : term (K_a ty) (S1 n)) (args : term (K_al tys) (S1 n)) (s : term K_s (S2 n m)) : 
    (T_al_cons a args)[: s ] =σ T_al_cons (a[: s]) (args[: s ])
| aeq_subst_abase {n m} b x (s : term K_s (S2 n m)) : 
    (T_abase b x)[: s ] =σ T_abase b x
| aeq_subst_aterm {n m} (t : term K_t (S1 n)) (s : term K_s (S2 n m)) : 
    (T_aterm t)[: s ] =σ T_aterm (t[: s ])
| aeq_subst_abind {n m ty} (a : term (K_a ty) (S1 (S n))) (s : term K_s (S2 n m)) : 
    (T_abind a)[: s ] =σ T_abind (a[: up_subst s ])
| aeq_subst_subst {n m o k} (t : term k (S1 n)) (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) :
    t[: s1 ][: s2 ] =σ t[: s1 >> s2 ]
| aeq_subst_t_mvar {n k} (v : mvar k (S1 n)) :
    (T_mvar v)[: sid ] =σ T_mvar v 

(** Substitution laws. *)

| aeq_sshift_succ {n} k : 
    @T_sshift n (S k) =σ ↑k >> ↑1
| aeq_sshift_scons {n} :
  T_var (@fin_zero n) .: ↑1 =σ ↑0  
| aeq_sid_l {n m} (s : term K_s (S2 n m)) : 
    sid >> s =σ s 
| aeq_sid_r {n m} (s : term K_s (S2 n m)) : 
    s >> sid =σ s 
| aeq_assoc {n m o p} (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) (s3 : term K_s (S2 o p)) : 
    s1 >> (s2 >> s3) =σ (s1 >> s2) >> s3
| aeq_distrib {n m o} (t : term K_t (S1 m)) (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) : 
    (t .: s1) >> s2 =σ t[: s2 ] .: s1 >> s2

where "t1 '=σ' t2" := (axiom_eq t1 t2).
Hint Constructors axiom_eq : core.

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

#[global] Instance axiom_eq_equiv k s : Equivalence (@axiom_eq k s).
Proof. constructor ; eauto. Qed.

#[global] Instance t_ctor_proper n c : Proper (axiom_eq ==> axiom_eq) (@T_ctor n c).
Proof. intros ???. apply aeq_congr_ctor ; auto. Qed.

#[global] Instance t_al_cons_proper n ty tys : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@T_al_cons n ty tys).
Proof. intros ??????. apply aeq_congr_al_cons ; auto. Qed.

#[global] Instance t_aterm_proper n : Proper (axiom_eq ==> axiom_eq) (@T_aterm n).
Proof. intros ???. apply aeq_congr_aterm ; auto. Qed.

#[global] Instance t_abind_proper n ty : Proper (axiom_eq ==> axiom_eq) (@T_abind n ty).
Proof. intros ???. apply aeq_congr_abind ; auto. Qed.

#[global] Instance t_subst_proper n m k : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@T_subst n m k).
Proof. intros ??????. apply aeq_congr_subst ; auto. Qed.

#[global] Instance t_scons_proper n m : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@T_scons n m).
Proof. intros ??????. apply aeq_congr_scons ; auto. Qed.

#[global] Instance t_scomp_proper n m o : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@T_scomp n m o).
Proof. intros ??????. apply aeq_congr_scomp ; auto. Qed.


End Make.