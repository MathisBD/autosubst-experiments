From Prototype Require Import Prelude Sig.

Module Make (S : Sig).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Expressions (terms and substitutions). *)
(*********************************************************************************)

(** Expressions are indexed by kinds. *)
Inductive kind := 
| (** Term. *)
  Kt : kind
| (** Constructor argument. *)
  Ka : arg_ty -> kind
| (** List of constructor arguments. *)
  Kal : list arg_ty -> kind
| (** Substitution. *)
  Ks : kind.  
Derive NoConfusion for kind.

(** Expressions are indexed by a scope. *)
Inductive scope :=
| (** Scope of a expr, argument, or argument list. *)
  S1 : nat -> scope
| (** Scope of a substitution. *)
  S2 : nat -> nat -> scope.
Derive NoConfusion for scope.

(** An expression metavariable is encoded as a unique identifier (a natural).
    When denoting a expr, we have access to an environment which maps metavariable identifiers
    to actual (denoted) exprs. *)
Definition mvar (k : kind) (s : scope) := nat.

Reserved Notation "'term' n" (at level 0, n at level 0).
Reserved Notation "'arg' ty n" (at level 0, ty at level 0, n at level 0).
Reserved Notation "'args' tys n" (at level 0, tys at level 0, n at level 0).
Reserved Notation "'subst' n m" (at level 50, n at level 0, m at level 0).

(** Expressions over an abstract signature.
    Expressions are indexed by a kind and a scope. *)
Inductive expr : kind -> scope -> Type :=
| (** Term variable. *)
  E_var {n} : fin n -> term n
| (** Non-variable term constructor, applied to a list of arguments. *)
  E_ctor {n} : forall c, args (ctor_type S.t c) n -> term n
| (** Empty argument list. *)
  E_al_nil {n} : args [] n
| (** Non-empty argument list. *)
  E_al_cons {n ty tys} : arg ty n -> args tys n -> args (ty :: tys) n
| (** Base argument (e.g. bool or string). *)
  E_abase {n} : forall b, denote_base S.t b -> arg (AT_base b) n
| (** Term argument. *)
  E_aterm {n} : term n -> arg AT_term n
| (** Binder argument. *)
  E_abind {n ty} : arg ty (S n) -> arg (AT_bind ty) n
| (** Substitution applied to a term/argument/argument-list. *)
  E_subst {n m k} : expr k (S1 n) -> subst n m -> expr k (S1 m)
| (** Shift substitution. *)
  E_sshift {n} : forall k, subst n (k + n)
| (** Cons substitution. *)
  E_scons {n m} : term m -> subst n m -> subst (S n) m
| (** Composition of substitutions. *)
  E_scomp {n m o} : subst n m -> subst m o -> subst n o
| (** Metavariable. *)
  E_mvar {k s} : mvar k s -> expr k s
where "'term' n" := (expr Kt (S1 n))
  and "'arg' ty n" := (expr (Ka ty) (S1 n))
  and "'args' tys n" := (expr (Kal tys) (S1 n))
  and "'subst' n m" := (expr Ks (S2 n m)).
Derive Signature NoConfusion for expr.

Notation "↑ k" := (E_sshift k) (at level 0).
Notation "t .: s" := (E_scons t s) (at level 60, right associativity).
Notation "s1 >> s2" := (E_scomp s1 s2) (at level 50, left associativity).
Notation "t '[:' s ']'" := (E_subst t s) (at level 15, s at level 0, no associativity).

(** The identity substitution. *)
Definition sid {n} : subst n n := E_sshift 0.

(** Lift a substitution through a binder. *)
Equations up_subst {n m} (s : subst n m) : subst (S n) (S m) :=
up_subst s := E_var fin_zero .: s >> ↑1.

(*********************************************************************************)
(** *** Axiomatic equality. *)
(*********************************************************************************)

(** [e =σ e'] means that the expressions [e] and [e'] are equal 
    modulo the equational theory of sigma calculus. *)
Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
Inductive axiom_eq : forall {k s}, expr k s -> expr k s -> Prop :=

(** Equivalence. *)

| aeq_refl {k s} (e : expr k s) : e =σ e
| aeq_sym {k s} (e1 e2 : expr k s) : e1 =σ e2 -> e2 =σ e1
| aeq_trans {k s} (e1 e2 e3 : expr k s) : e1 =σ e2 -> e2 =σ e3 -> e1 =σ e3

(** Congruence. *)

| aeq_congr_ctor {n} c (al1 al2 : args _ n) : 
    al1 =σ al2 -> E_ctor c al1 =σ E_ctor c al2
| aeq_congr_al_cons {n ty tys} (a1 a2 : arg ty n) (al1 al2 : args tys n) : 
    a1 =σ a2 -> al1 =σ al2 -> E_al_cons a1 al1 =σ E_al_cons a2 al2
| aeq_congr_aterm {n} (t1 t2 : term n) : 
    t1 =σ t2 -> E_aterm t1 =σ E_aterm t2
| aeq_congr_abind {n ty} (a1 a2 : arg ty (S n)) : 
    a1 =σ a2 -> E_abind a1 =σ E_abind a2
| aeq_congr_subst {n m k} (t1 t2 : expr k (S1 n)) (s1 s2 : subst n m) : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 
| aeq_congr_scons {n m} (t1 t2 : term m) (s1 s2 : subst n m) : 
    t1 =σ t2 -> s1 =σ s2 -> t1 .: s1 =σ t2 .: s2
| aeq_congr_scomp {n m o} (s1 s2 : subst n m) (r1 r2 : subst m o) : 
    s1 =σ s2 -> r1 =σ r2 -> s1 >> r1 =σ s2 >> r2

(** Apply a substitution to a variable. *)

| aeq_sshift_var {n} (i : fin n) k : 
    (E_var i)[: ↑k ] =σ E_var (fin_weaken k i)
| aeq_scons_zero {n m} (t : term m) (s : subst n m) :
    (E_var fin_zero)[: t .: s] =σ t
| aeq_scons_succ {n m} (i : fin n) (t : term m) (s : subst n m) :
    (E_var (fin_succ i))[: t .: s] =σ (E_var i)[: s]

(** Apply a substitution to a expr. *)

| aeq_subst_ctor {n m} c (al : args _ n) (s : subst n m) : 
    (E_ctor c al)[: s ] =σ E_ctor c (al[: s ])
| aeq_subst_al_nil {n m} (s : subst n m) : 
    E_al_nil[: s ] =σ E_al_nil
| aeq_subst_al_cons {n m ty tys} (a : arg ty n) (al : args tys n) (s : subst n m) : 
    (E_al_cons a al)[: s ] =σ E_al_cons (a[: s]) (al[: s ])
| aeq_subst_abase {n m} b x (s : subst n m) : 
    (E_abase b x)[: s ] =σ E_abase b x
| aeq_subst_aterm {n m} (t : term n) (s : subst n m) : 
    (E_aterm t)[: s ] =σ E_aterm (t[: s ])
| aeq_subst_abind {n m ty} (a : arg ty (S n)) (s : subst n m) : 
    (E_abind a)[: s ] =σ E_abind (a[: up_subst s ])
| aeq_subst_subst {n m o k} (t : expr k (S1 n)) (s1 : subst n m) (s2 : subst m o) :
    t[: s1 ][: s2 ] =σ t[: s1 >> s2 ]
| aeq_subst_t_mvar {n k} (v : mvar k (S1 n)) :
    (E_mvar v)[: sid ] =σ E_mvar v 

(** Substitution laws. *)

| aeq_sshift_succ_r {n} k : 
    ↑k >> ↑1 =σ @E_sshift n (S k)
| aeq_sshift_scons {n} :
    E_var (@fin_zero n) .: ↑1 =σ ↑0  
| aeq_scons_sshift {n m} (t : term m) (s : subst n m) :
  ↑1 >> (t .: s) =σ s
| aeq_sid_l {n m} (s : subst n m) : 
    sid >> s =σ s 
| aeq_sid_r {n m} (s : subst n m) : 
    s >> sid =σ s 
| aeq_assoc {n m o p} (s1 : subst n m) (s2 : subst m o) (s3 : subst o p) : 
    s1 >> (s2 >> s3) =σ (s1 >> s2) >> s3
| aeq_distrib {n m o} (t : term m) (s1 : subst n m) (s2 : subst m o) : 
    (t .: s1) >> s2 =σ t[: s2 ] .: s1 >> s2

where "t1 '=σ' t2" := (axiom_eq t1 t2).
Hint Constructors axiom_eq : core.

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

#[global] Instance axiom_eq_equiv k s : Equivalence (@axiom_eq k s).
Proof. constructor ; eauto. Qed.

#[global] Instance t_ctor_proper n c : Proper (axiom_eq ==> axiom_eq) (@E_ctor n c).
Proof. intros ???. apply aeq_congr_ctor ; auto. Qed.

#[global] Instance t_al_cons_proper n ty tys : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_al_cons n ty tys).
Proof. intros ??????. apply aeq_congr_al_cons ; auto. Qed.

#[global] Instance t_aterm_proper n : Proper (axiom_eq ==> axiom_eq) (@E_aterm n).
Proof. intros ???. apply aeq_congr_aterm ; auto. Qed.

#[global] Instance t_abind_proper n ty : Proper (axiom_eq ==> axiom_eq) (@E_abind n ty).
Proof. intros ???. apply aeq_congr_abind ; auto. Qed.

#[global] Instance t_subst_proper n m k : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_subst n m k).
Proof. intros ??????. apply aeq_congr_subst ; auto. Qed.

#[global] Instance t_scons_proper n m : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_scons n m).
Proof. intros ??????. apply aeq_congr_scons ; auto. Qed.

#[global] Instance t_scomp_proper n m o : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_scomp n m o).
Proof. intros ??????. apply aeq_congr_scomp ; auto. Qed.

(*********************************************************************************)
(** *** Additional functions and properties. *)
(*********************************************************************************)

End Make.