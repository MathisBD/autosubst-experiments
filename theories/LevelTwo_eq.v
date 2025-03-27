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

(*********************************************************************************)
(** *** Normal forms. *)
(*********************************************************************************)

(** A term is in normal form if and only if:
    - metavariables always appear to the left of a substitution or composition.
    - no other term appears to the left of a substitution or composition. *)
Inductive nf : forall {k s}, term k s -> Prop :=
(** Structural rules. *)
| nf_tvar {n} (i : fin n) : 
    nf (T_var i)
| nf_tctor {n} c (args : term _ (S1 n)) : 
    nf args -> nf (T_ctor c args) 
| nf_al_nil {n} : 
    nf (@T_al_nil n)
| nf_al_cons {n ty tys} (a : term (K_a ty) (S1 n)) (args : term (K_al tys) (S1 n)) :
    nf a -> nf args -> nf (T_al_cons a args)
| nf_abase {n} b x :
    nf (@T_abase n b x) 
| nf_aterm {n} (t : term K_t (S1 n)) :
    nf t -> nf (T_aterm t)
| nf_abind {n ty} (a : term (K_a ty) (S1 (S n))) :
    nf a -> nf (T_abind a)
| nf_sshift {n k} : 
    nf (@T_sshift n k)
| nf_scons {n m} (t : term K_t (S1 m)) (s : term K_s (S2 n m)) : 
    nf t -> nf s -> nf (t .: s)
(** Substitution and composition rules. *)
| nf_subst_t {n m k} (xt : mvar k (S1 n)) (s : term K_s (S2 n m)) : 
    nf (T_mvar xt [: s ])
| nf_subst_s {n m o k} (xs : mvar K_s (S2 (k + S n) m)) (s : term K_s (S2 m o)) :
    nf s -> nf (T_var fin_zero [: ↑k >> T_mvar xs ][: s])
| nf_scomp {n m o k} (v : mvar K_s (S2 (k + n) m)) (s : term K_s (S2 m o)) :
    nf s -> nf (↑k >> T_mvar v >> s).
Hint Constructors nf : core.

(*********************************************************************************)
(** *** Term/substitution simplification. *)
(*********************************************************************************)

(*

apply_subst : fin n -> subst n m -> term K_t m
apply_subst i (shift k) := T_var (i + k)
apply_subst 0 (t .: s) := t
apply_subst (S i) (t .: s) := apply_subst i s
apply_subst i (s1 >> s2) := push_subst (apply_subst i s1) s2

push_subst : term k n -> subst n m -> term k m
push_subst (T_var i) s := apply_subst i s
push_subst (T_ctor c args) s := T_ctor c (push_subst args s)
push_subst T_al_nil s := T_al_nil
push_subst (T_al_cons a args) s := T_al_cons (push_subst a s) (push_subst args s)
push_subst (T_abase b x) := T_abase b x
push_subst (T_aterm t) s := T_aterm (push_subst t s)
push_subst (T_abind a) s := T_abind (push_subst a (up_subst s))
push_subst (t[s]) s' := t[simpl_comp s s']

simpl_comp : subst n m -> subst m o -> subst n o
simpl_comp (shift 0) s := s
simpl_comp (shift (S i)) s := push_shift (simpl_comp (shift i) s)
simpl_comp (t .: s) s' := t[s'] .: (s >> s')
simpl_comp (s1 >> s2) s3 := s1 >> simpl_comp s2 s3

push_shift : subst (S n) m -> subst n m
push_shift (shift i) := shift (S i)
push_shift (t .: s) := s
push_shift (s1 >> s2) := simpl_comp (push_shift s1) s2

*)

(** Head of a normal form substitution. *)
Equations head {n m} (s : term K_s (S2 (S n) m)) : term K_t (S1 m) :=
head (↑ k) := T_var (fin_weaken k fin_zero) ;
head (t .: _) := t ;
head (↑k >> T_mvar xs >> s) := T_var fin_zero [: ↑k >> T_mvar xs ] [: s ] ;
head s := T_var fin_zero [: s ].

Lemma head_sound {n m} (s : term K_s (S2 (S n) m)) :
  head s =σ T_var fin_zero [: s ].
Proof. funelim (head s) ; simp head in * ; auto. Qed.

Lemma head_nf {n m} (s : term K_s (S2 (S n) m)) :
  nf s -> nf (head s).
Proof. intros H. dependent elimination H ; simp head ; auto. Qed.

(** Tail of a normal form substitution. *)
Equations tail {n m} (s : term K_s (S2 (S n) m)) : term K_s (S2 n m) :=
tail (↑ k) := _ ;
tail (_ .: s) := s ;
tail (↑k >> T_mvar xs >> s) := _ >> T_mvar xs >> s ;
tail s := ↑1 >> s.
Next Obligation. rewrite PeanoNat.Nat.add_succ_r. exact (↑ (S k)). Defined.
Next Obligation. rewrite PeanoNat.Nat.add_succ_r. exact (↑ (S k)). Defined.

Lemma tail_sound {n m} (s : term K_s (S2 (S n) m)) :
  tail s =σ ↑1 >> s.
Proof. 
funelim (tail s) ; simp tail in * ; auto.
Admitted.

Lemma tail_nf {n m} (s : term K_s (S2 (S n) m)) :
  nf s -> nf (tail s).
Proof. intros H. dependent elimination H ; simp tail ; auto. Admitted.

(** Apply a normal form substitution to a variable. *)
Equations apply_subst {n m} (i : fin n) (s : term K_s (S2 n m)) : term K_t (S1 m) :=
apply_subst fin_zero s := head s ;
apply_subst (fin_succ i) s := apply_subst i (tail s).

Lemma apply_subst_sound {n m} (i : fin n) (s : term K_s (S2 n m)) :
  apply_subst i s =σ T_var i [: s ].
Proof. 
funelim (apply_subst i s).
- now rewrite head_sound.
- rewrite H. rewrite tail_sound. rewrite <-aeq_subst_subst, aeq_sshift_var.
  reflexivity.
Qed.

Lemma apply_subst_nf {n m} (i : fin n) (s : term K_s (S2 n m)) :
  nf s -> nf (apply_subst i s).
Proof. 
intros H. funelim (apply_subst i s) ; simp apply_subst.
- now apply head_nf.
- apply H. now apply tail_nf.
Qed.

(** Apply a normal form substitution to a normal form term. *)
Equations simpl_subst {k n m} (t : term k (S1 n)) (s : term K_s (S2 n m)) : term k (S1 m) :=
simpl_subst (T_var i) s := apply_subst i s ;
simpl_subst (T_ctor c args) s := T_ctor c (simpl_subst args s) ;
simpl_subst T_al_nil _ := T_al_nil ;
simpl_subst (T_al_cons a args) s := T_al_cons (simpl_subst a s) (simpl_subst args s) ;
simpl_subst (T_abase b x) s := T_abase b x ;
simpl_subst (T_aterm t) s := T_aterm (simpl_subst t s) ;
simpl_subst (T_abind a) s := T_abind (simpl_subst a (T_var fin_zero .: simpl_comp s (↑1))) ;
simpl_subst (T_subst t s1) s2 := T_subst t (simpl_comp s1 s2) ;
simpl_subst (T_mvar xt) s := T_subst (T_mvar xt) s
(** Compose normal form substitutions. *)
with simpl_comp {n m o} (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) : term K_s (S2 n o) :=
simpl_comp (↑k) s := (↑k) >> s ;
simpl_comp (t1 .: s1) s2 := simpl_subst t1 s2 .: simpl_comp s1 s2 ;
simpl_comp (s1 >> s1') s2 := s1 >> (simpl_comp s1' s2) ;
simpl_comp (T_mvar xs) s := (T_mvar xs) >> s.

(*Fixpoint simpl_subst {k n m} (t : term k (S1 n)) (s : term K_s (S2 n m)) {struct t} : term k (S1 m)
    with simpl_comp {n m o} (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) {struct s1} : term K_s (S2 n o).
(* simpl_subst. *)
- dependent destruction t. 
  + exact (T_subst (T_var f) s).
  + exact (T_ctor c (simpl_subst _ _ _ t s)).
  + exact (T_al_nil).
  + exact (T_al_cons (simpl_subst _ _ _ t1 s) (simpl_subst _ _ _ t2 s)).
  + exact (T_abase b d).
  + exact (T_aterm (simpl_subst _ _ _ t s)).
  + exact (T_abind (simpl_subst _ _ _ t (up_subst s))).
  + exact (T_subst t1 (simpl_comp _ _ _ t2 s)).
(* simpl_comp. *)
- dependent destruction s1.
  + exact (T_scomp (T_sshift k) s2).
  + exact (T_scons (simpl_subst _ _ _ s1_1 s2) (simpl_comp _ _ _ s1_2 s2)).
  + exact (T_scomp s1_1 (simpl_comp _ _ _ s1_2 s2)).
Qed.  *)   


Lemma simpl_subst_sound {k n m} (t : term k (S1 n)) (s : term K_s (S2 n m)) :
  simpl_subst t s =σ T_subst t s.
Proof. Admitted.

Definition simpl {k s} (t : term k s) : term k s.
dependent induction t.
- exact (T_var f).
- exact (T_ctor c IHt).
- exact (T_al_nil).
- exact (T_al_cons IHt1 IHt2).
- exact (T_abase b d).
- exact (T_aterm IHt).
- exact (T_abind IHt).
- exact (simpl_subst t1 t2).
- exact (T_sshift k).
- exact (T_scons IHt1 IHt2).
- exact (T_scomp IHt1 IHt2).
Defined.  

Lemma up_subst_sid n : up_subst (@sid n) =σ sid.
Proof. 
cbv [up_subst sid]. simpl. setoid_rewrite <-(aeq_sshift_succ 0).
setoid_rewrite aeq_sshift_scons. reflexivity.
Qed.

Lemma subst_sid k n (t : term k (S1 n)) : t[: sid] =σ t.
Proof.
dependent induction t generalizing n ; try (now auto).
- unfold sid. rewrite (aeq_sshift_var f 0). reflexivity.
- rewrite aeq_subst_ctor. rewrite IHt ; auto.
- rewrite aeq_subst_al_cons. rewrite IHt1, IHt2 ; auto.
- rewrite aeq_subst_aterm. rewrite IHt ; auto.
- rewrite aeq_subst_abind. rewrite up_subst_sid. rewrite IHt ; auto.
- setoid_rewrite aeq_subst_subst. rewrite aeq_sid_r. reflexivity.
Qed. 

(** Main property: [simpl] is sound. *)
Lemma simpl_sound {k s} (t : term k s) : simpl t =σ t.
Proof.
dependent induction t ; simpl ; try auto.
- now rewrite simpl_subst_sound.
- rewrite IHt1, IHt2. reflexivity.
- rewrite IHt1, IHt2. reflexivity. 
Qed.

(** This lemma is a simple consequence of the soundness of [simpl]. 
    We could also prove it directly by induction, e.g. if we need it to prove 
    the soundness of [simpl]. *)
#[global] Instance simpl_proper k s : Proper (axiom_eq ==> axiom_eq) (@simpl k s).
Proof. intros ???. rewrite simpl_sound, simpl_sound. assumption. Qed.

End Make.