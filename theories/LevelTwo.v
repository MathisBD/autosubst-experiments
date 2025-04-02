From Prototype Require Import Prelude Sig.

Module Make (S : Sig).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Expressions (terms and substitutions). *)
(*********************************************************************************)

(** Kind of a term, argument, or argument list. *)
Inductive mono_kind :=
| (** Term. *)
  Kt : mono_kind
| (** Constructor argument. *)
  Ka : arg_ty -> mono_kind
| (** List of constructor arguments. *)
  Kal : list arg_ty -> mono_kind.
Derive NoConfusion for mono_kind.

(** Expressions are indexed by kinds. *)
Inductive kind : Type := 
| (** Term, argument, or argument list. *)
  Km : mono_kind -> kind
| (** Substitution. *)
  Ks : kind.  
Derive NoConfusion for kind.

(** An expression metavariable is encoded as a unique identifier (a natural).
    When denoting a expr, we have access to an environment which maps metavariable identifiers
    to actual (denoted) expressions. *)
Definition mvar (k : kind) := nat.

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).
Reserved Notation "'subst'" (at level 0).

(** Expressions over an abstract signature. 
    Expressions are indexed by a kind: this is to avoid writing a mutual inductives,
    which would be hard to manipulate. *)
Inductive expr : kind -> Type :=
| (** Term variable. *)
  E_var : nat -> term
| (** Non-variable term constructor, applied to a list of arguments. *)
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
| (** Substitution applied to a term/argument/argument-list. *)
  E_subst {k} : expr (Km k) -> subst -> expr (Km k)
| (** Shift substitution. *)
  E_sshift : nat -> subst
| (** Substitution expansion. *)
  E_scons : term -> subst -> subst
| (** Substitution composition. *)
  E_scomp : subst -> subst -> subst
| (** Metavariable. *)
  E_mvar {k} : mvar k -> expr k
where "'term'" := (expr (Km Kt))
  and "'arg' ty" := (expr (Km (Ka ty)))
  and "'args' tys" := (expr (Km (Kal tys)))
  and "'subst'" := (expr Ks).
Derive Signature NoConfusion for expr.

(** Notations for common expressions. *)
Notation "↑ k" := (E_sshift k) (at level 0, k at level 0).
Notation "t .: s" := (E_scons t s) (at level 60, right associativity).
Notation "s1 >> s2" := (E_scomp s1 s2) (at level 50, left associativity).
Notation "t '[:' s ']'" := (E_subst t s) (at level 15, s at level 0, no associativity).

(** The identity substitution. *)
Definition sid : subst := E_sshift 0.

(** Lift a substitution through a binder. *)
Equations up_subst (s : subst) : subst :=
up_subst s := E_var 0 .: s >> ↑1.

(*********************************************************************************)
(** *** Axiomatic equality. *)
(*********************************************************************************)

(** [e =σ e'] means that the expressions [e] and [e'] are equal 
    modulo the equational theory of sigma calculus. *)
Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
Inductive axiom_eq : forall {k}, expr k -> expr k -> Prop :=

(** Equivalence. *)

| aeq_refl {k} (e : expr k) : e =σ e
| aeq_sym {k} (e1 e2 : expr k) : e1 =σ e2 -> e2 =σ e1
| aeq_trans {k} (e1 e2 e3 : expr k) : e1 =σ e2 -> e2 =σ e3 -> e1 =σ e3

(** Congruence. *)

| aeq_congr_ctor c (al1 al2 : args _) : 
    al1 =σ al2 -> E_ctor c al1 =σ E_ctor c al2
| aeq_congr_al_cons {ty tys} (a1 a2 : arg ty) (al1 al2 : args tys) : 
    a1 =σ a2 -> al1 =σ al2 -> E_al_cons a1 al1 =σ E_al_cons a2 al2
| aeq_congr_aterm (t1 t2 : term) : 
    t1 =σ t2 -> E_aterm t1 =σ E_aterm t2
| aeq_congr_abind {ty} (a1 a2 : arg ty) : 
    a1 =σ a2 -> E_abind a1 =σ E_abind a2
| aeq_congr_subst {k} (t1 t2 : expr (Km k)) (s1 s2 : subst) : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 
| aeq_congr_scons (t1 t2 : term) (s1 s2 : subst) : 
    t1 =σ t2 -> s1 =σ s2 -> t1 .: s1 =σ t2 .: s2
| aeq_congr_scomp (s1 s2 s1' s2' : subst) : 
    s1 =σ s2 -> s1' =σ s2' -> s1 >> s1' =σ s2 >> s2'

(** Apply a substitution to a variable. *)

| aeq_sshift_var i k : 
    (E_var i)[: ↑k ] =σ E_var (k + i)
| aeq_scons_zero (t : term) (s : subst) :
    (E_var 0)[: t .: s] =σ t
| aeq_scons_succ i (t : term) (s : subst) :
    (E_var (S i))[: t .: s] =σ (E_var i)[: s]

(** Apply a substitution to an expression. *)

| aeq_subst_ctor c (al : args _) (s : subst) : 
    (E_ctor c al)[: s ] =σ E_ctor c (al[: s ])
| aeq_subst_al_nil (s : subst) : 
    E_al_nil[: s ] =σ E_al_nil
| aeq_subst_al_cons {ty tys} (a : arg ty) (al : args tys) (s : subst) : 
    (E_al_cons a al)[: s ] =σ E_al_cons (a[: s]) (al[: s ])
| aeq_subst_abase b x (s : subst) : 
    (E_abase b x)[: s ] =σ E_abase b x
| aeq_subst_aterm (t : term) (s : subst) : 
    (E_aterm t)[: s ] =σ E_aterm (t[: s ])
| aeq_subst_abind {ty} (a : arg ty) (s : subst) : 
    (E_abind a)[: s ] =σ E_abind (a[: up_subst s ])
| aeq_subst_subst {k} (e : expr (Km k)) (s1 s2 : subst) :
    e[: s1 ][: s2 ] =σ e[: s1 >> s2 ]
| aeq_subst_mvar {k} (v : mvar (Km k)) :
    (E_mvar v)[: sid ] =σ E_mvar v 

(** Substitution laws. *)

| aeq_sshift_succ_r k : 
    ↑k >> ↑1 =σ ↑(S k)
| aeq_sshift_scons :
    E_var 0 .: ↑1 =σ ↑0  
| aeq_scons_sshift (t : term) (s : subst) :
  ↑1 >> (t .: s) =σ s
| aeq_sid_l (s : subst) : 
    sid >> s =σ s 
| aeq_sid_r (s : subst) : 
    s >> sid =σ s
| aeq_assoc (s1 s2 s3 : subst) : 
    s1 >> (s2 >> s3) =σ (s1 >> s2) >> s3
| aeq_distrib (t : term) (s1 s2 : subst) : 
    (t .: s1) >> s2 =σ t[: s2 ] .: s1 >> s2

where "t1 '=σ' t2" := (axiom_eq t1 t2).
Hint Constructors axiom_eq : core.

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

#[global] Instance axiom_eq_equiv k : Equivalence (@axiom_eq k).
Proof. constructor ; eauto. Qed.

#[global] Instance e_ctor_proper c : Proper (axiom_eq ==> axiom_eq) (@E_ctor c).
Proof. intros ???. apply aeq_congr_ctor ; auto. Qed.

#[global] Instance e_al_cons_proper ty tys : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_al_cons ty tys).
Proof. intros ??????. apply aeq_congr_al_cons ; auto. Qed.

#[global] Instance e_aterm_proper : Proper (axiom_eq ==> axiom_eq) E_aterm.
Proof. intros ???. apply aeq_congr_aterm ; auto. Qed.

#[global] Instance e_abind_proper ty : Proper (axiom_eq ==> axiom_eq) (@E_abind ty).
Proof. intros ???. apply aeq_congr_abind ; auto. Qed.

#[global] Instance e_subst_proper k : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_subst k).
Proof. intros ??????. apply aeq_congr_subst ; auto. Qed.

#[global] Instance e_scons_proper : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) E_scons.
Proof. intros ??????. apply aeq_congr_scons ; auto. Qed.

#[global] Instance e_scomp_proper : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) E_scomp.
Proof. intros ??????. apply aeq_congr_scomp ; auto. Qed.

(*********************************************************************************)
(** *** Additional functions and properties. *)
(*********************************************************************************)

Lemma up_subst_sid : up_subst sid =σ sid.
Proof. autorewrite with up_subst. rewrite aeq_sid_l. now rewrite aeq_sshift_scons. Qed.

Lemma aeq_sshift_succ_l k : ↑1 >> ↑k =σ ↑(S k).
Proof. 
induction k as [|k IHk].
- rewrite aeq_sid_r. reflexivity.
- rewrite <-(aeq_sshift_succ_r k). rewrite aeq_assoc.
  rewrite IHk, aeq_sshift_succ_r. reflexivity.
Qed.  

Lemma aeq_sshift_plus k l : ↑k >> ↑l =σ ↑(k + l).
Proof.
revert l ; induction k as [|k IHk] ; intro l.
- simpl. rewrite aeq_sid_l. reflexivity.
- simpl. rewrite <-(aeq_sshift_succ_r (k + l)). rewrite <-IHk.
  rewrite <-aeq_sshift_succ_r. rewrite <-aeq_assoc, <-aeq_assoc.
  now rewrite aeq_sshift_succ_l, aeq_sshift_succ_r.
Qed.

Lemma aeq_sshift_comm k l : ↑k >> ↑l =σ ↑l >> ↑k.
Proof. 
rewrite aeq_sshift_plus, aeq_sshift_plus. 
now rewrite PeanoNat.Nat.add_comm. 
Qed.
    
Lemma aeq_subst_sid {k} (e : expr (Km k)) : e[: sid ] =σ e.
Proof. 
dependent induction e ; auto.  
- setoid_rewrite aeq_sshift_var. reflexivity.
- now rewrite aeq_subst_ctor, IHe.
- now rewrite aeq_subst_al_cons, IHe1, IHe2.
- now rewrite aeq_subst_aterm, IHe.
- now rewrite aeq_subst_abind, up_subst_sid, IHe.
- rewrite aeq_subst_subst. now rewrite aeq_sid_r.
Qed.

End Make.