From Prototype Require Import Prelude Sig.

Section WithSig.
Context (sig : signature).
Definition arg_ty := @arg_ty (base sig).

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

(** Terms and substitutions are indexed by a scope. *)
Inductive scope :=
| (** Scope of a term, argument, or argument list. *)
  S1 : nat -> scope
| (** Scope of a substitution. *)
  S2 : nat -> nat -> scope.

(** Terms over an abstract signature. 
    Terms are indexed by a kind and a scope. *)
Inductive term : kind -> scope -> Type :=
| (** Term variable. *)
  T_var {n} : fin n -> term K_t (S1 n)
| (** Non-variable term constructor, applied to a list of arguments. *)
  T_ctor {n} : forall c, term (K_al (ctor_type sig c)) (S1 n) -> term K_t (S1 n)
| (** Empty argument list. *)
  T_al_nil {n} : term (K_al []) (S1 n)
| (** Non-empty argument list. *)
  T_al_cons {n ty tys} : term (K_a ty) (S1 n) -> term (K_al tys) (S1 n) -> term (K_al (ty :: tys)) (S1 n)
| (** Base argument (e.g. bool or string). *)
  T_abase {n} : forall b, denote_base sig b -> term (K_a (AT_base b)) (S1 n)
| (** Term argument. *)
  T_aterm {n} : term K_t (S1 n) -> term (K_a AT_term) (S1 n)
| (** Binder argument. *)
  T_abind {n ty} : term (K_a ty) (S1 (S n)) -> term (K_a (AT_bind ty)) (S1 n)
| (** Substitution applied to a term/argument/argument list. *)
  T_subst {n m k} : term k (S1 n) -> term K_s (S2 n m) -> term k (S1 m)
(*| T_mvar {s k} : mvar k s -> term k s*)
| (** Shift substitution. *)
  T_sshift {n} : forall k, term K_s (S2 n (k + n))
| (** Cons substitution. *)
  T_scons {n m} : term K_t (S1 m) -> term K_s (S2 n m) -> term K_s (S2 (S n) m)
| (** Composition of substitutions. *)
  T_scomp {n m o} : term K_s (S2 n m) -> term K_s (S2 m o) -> term K_s (S2 n o).

(** The identity substitution. *)
Definition sid {n} : term K_s (S2 n n) := T_sshift 0.

#[global] Instance subst_notation (n m : nat) (k : kind) :
  Subst (term k (S1 n)) (term K_s (S2 n m)) (term k (S1 m)) :=
{ gen_subst := T_subst }.

#[global] Instance scons_notation (n m : nat) : 
  Scons (term K_t (S1 m)) (term K_s (S2 n m)) (term K_s (S2 (S n) m)) :=
{ gen_scons := T_scons }.

#[global] Instance scomp_notation (n m o : nat) : 
  Scomp (term K_s (S2 n m)) (term K_s (S2 m o)) (term K_s (S2 n o)) :=
{ gen_scomp := T_scomp }.

(*********************************************************************************)
(** *** Axiomatic equality. *)
(*********************************************************************************)

(** [t σ= t'] means that the terms/substitutions [t] and [t'] are equal 
    modulo the equational theory of sigma calculus. *)
Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
Inductive axiom_eq : forall {k s}, term k s -> term k s -> Prop :=

(** Equivalence. *)

| aeq_refl {k s} (t : term k s) : t =σ t
| aeq_sym {k s} (t1 t2 : term k s) : t1 =σ t2 -> t2 =σ t1
| aeq_trans {k s} (t1 t2 t3 : term k s) : t1 =σ t2 -> t2 =σ t3 -> t1 =σ t3

(** Congruence. *)

| aeq_t_ctor {n} c (args1 args2 : term _ (S1 n)) : 
    args1 =σ args2 -> T_ctor c args1 =σ T_ctor c args2
| aeq_t_subst {n m k} (t1 t2 : term k (S1 n)) (s1 s2 : term K_s (S2 n m)) : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 

(*| aeq_al_cons ty tys (a1 a2 : term (A ty)) (args1 args2 : term (AL tys)) : 
    a1 =σ a2 -> args1 =σ args2 -> AL_cons a1 args1 =σ AL_cons a2 args2
| aeq_al_subst tys (args1 args2 : term (AL tys)) s1 s2 :
    args1 =σ args2 -> s1 =σ s2 -> args1[: s1] =σ args2[: s2]

| aeq_a_term t1 t2 : t1 =σ t2 -> A_term t1 =σ A_term t2
| aeq_a_bind ty (a1 a2 : term (A ty)) : a1 =σ a2 -> A_bind a1 =σ A_bind a2
| aeq_a_subst ty (a1 a2 : term (A ty)) s1 s2 :
    a1 =σ a2 -> s1 =σ s2 -> a1[: s1] =σ a2[: s2]

| seq_s_cons t1 t2 s1 s2 : 
    t1 =σ t2 -> s1 =σ s2 -> t1 .: s1 =σ t2 .: s2
| seq_s_comp s1 s2 r1 r2 : 
    s1 =σ s2 -> r1 =σ r2 -> s1 ∘ r1 =σ s2 ∘ r2

(** Sigma equations. *)

| seq_push_subst_var n s : (T_var n)[: s] =σ apply_subst s n
| seq_push_subst_ctor c args s : (T_ctor c args)[: s] =σ T_ctor c (args[: s])
| seq_push_subst_al_nil s : AL_nil[: s] =σ AL_nil
| seq_push_subst_al_cons ty tys (a : term (A ty)) (args : term (AL tys)) s : 
    (AL_cons a args)[: s] =σ AL_cons (a[: s]) (args[: s])
| seq_push_subst_a_base b x s : (A_base b x)[: s] =σ A_base b x
| seq_push_subst_a_term t s : (A_term t)[: s] =σ A_term (t[: s])
| seq_push_subst_a_bind ty (a : term (A ty)) s : 
    (A_bind a)[: s] =σ A_bind (a[: T_var 0 .: S_shift 1 ∘ s])

| seq_shift k : S_shift (k+1) =σ S_shift 1 ∘ S_shift k 
| seq_id_left s : S_id ∘ s =σ s 
| seq_id_right s : s ∘ S_id =σ s 
| seq_assoc s1 s2 s3 : s1 ∘ (s2 ∘ s3) =σ (s1 ∘ s2) ∘ s3
| seq_distrib t s1 s2 : s2 ∘ (t .: s1) =σ t[: s2 ] .: s2 ∘ s1*)

where "t1 '=σ' t2" := (axiom_eq t1 t2).
Hint Constructors axiom_eq  : core.


End WithSig.