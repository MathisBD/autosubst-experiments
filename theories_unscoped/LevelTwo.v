From Prototype Require Import Prelude Sig LevelOne.

Module Make (S : Sig).
Module O := LevelOne.Make (S).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Explicit renamings. *)
(*********************************************************************************)

(** Notations for common renamings. *)
Notation "'↑ᵣ' k" := (R_shift k) (at level 0, k at level 0).
Notation "i '.ᵣ' r" := (R_cons i r) (at level 60, right associativity).
Notation "r1 '>>ᵣ' r2" := (R_comp r1 r2) (at level 50, left associativity).

(*********************************************************************************)
(** *** Expressions (terms and explicit substitutions). *)
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

(** Kind of a renaming or substitution. *)
Inductive ren_kind :=
| (** *)

(** Expressions are indexed by kinds. *)
Inductive kind : Type := 
| (** Term-like. *)
  Km : mono_kind -> kind
| (** Substitution-like. *)
  Kb : bi_kind -> kind.  
Derive NoConfusion for kind.

Definition denote_type (k : kind) : Type :=
  match k with 
  | Km Kt => O.expr O.Kt
  | Km (Kal tys) => O.expr (O.Kal tys)
  | Km (Ka ty) => O.expr (O.Ka ty)
  | Ks => O.subst
  end.

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).
Reserved Notation "'subst'" (at level 0).

(** Expressions over an abstract signature. 
    Expressions are indexed by a kind: this is to avoid writing a mutual inductives,
    which would be hard to manipulate. *)
Inductive expr : kind -> Type :=
| (** Variable term constructor (de Bruijn index). *)
  T_var : nat -> term
| (** Non-variable term constructor, applied to a list of arguments. *)
  T_ctor : forall c, args (ctor_type S.t c) -> term

| (** Empty argument list. *)
  AL_nil : args []
| (** Non-empty argument list. *)
  AL_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

| (** Base argument (e.g. bool or string). *)
  A_base : forall b, denote_base S.t b -> arg (AT_base b)
| (** Term argument. *)
  A_term : term -> arg AT_term
| (** Binder argument. *)
  A_bind {ty} : arg ty -> arg (AT_bind ty)

| (** Shift renaming. *)
  R_shift : nat -> ren
| (** Renaming expansion. *)
  R_cons : nat -> ren -> ren
| (** Renaming composition. *)
  R_comp : ren -> ren -> ren

| (** Shift substitution. *)
  S_shift : nat -> subst
| (** Substitution expansion. *)
  S_cons : term -> subst -> subst
| (** Substitution composition. *)
  S_comp : subst -> subst -> subst
| (** View a renaming as a substitution. *)
  S_ren : ren -> subst

| (** Instantiate a term/argument/argument-list with a renaming. *)
  E_rinst {k} : expr (Km k) -> ren -> expr (Km k)
| (** Metavariable (of any kind). *)
  E_mvar {k} : denote_type k -> expr k

where "'term'" := (expr (Km Kt))
  and "'arg' ty" := (expr (Km (Ka ty)))
  and "'args' tys" := (expr (Km (Kal tys)))
  and "'subst'" := (expr Ks).

Derive Signature NoConfusion for expr.

(** Notations for common expressions. *)

Notation "'↑ₛ' k" := (S_shift k) (at level 0, k at level 0).
Notation "t '.ₛ' s" := (S_cons t s) (at level 60, right associativity).
Notation "s1 '>>ₛ' s2" := (S_comp s1 s2) (at level 50, left associativity).
Notation "t '[:' s ']'" := (E_inst t s) (at level 15, s at level 0, no associativity).

(** The identity renaming. *)
Definition rid : ren := R_shift 0.

(** The identity substitution. *)
Definition sid : subst := S_shift 0.

(** Lift a renaming through a binder. *)
Definition up_ren (r : ren) : ren :=
  0 .ᵣ r >>ᵣ ↑ᵣ1.

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  E_var 0 .ₛ s >>ₛ ↑ₛ1.

(*********************************************************************************)
(** *** Axiomatic equality. *)
(*********************************************************************************)

(** [e =σ e'] means that the expressions [e] and [e'] are equal 
    modulo the equational theory of sigma calculus. *)
(*Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
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
| aeq_congr_inst {k} (t1 t2 : expr (Km k)) (s1 s2 : subst) : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 
| aeq_congr_scons (t1 t2 : term) (s1 s2 : subst) : 
    t1 =σ t2 -> s1 =σ s2 -> t1 .ₛ s1 =σ t2 .ₛ s2
| aeq_congr_comp {k1 k2} (s1 s2 : expr (K2 k1)) (s1' s2' : expr (K2 k2)) : 
    s1 =σ s2 -> s1' =σ s2' -> s1 >> s1' =σ s2 >> s2'

(** Apply a renaming to a variable. *)

| aeq_rshift_var i k : 
    (E_var i)[ᵣ ↑ᵣ k ] =σ E_var (k + i)
| aeq_rcons_zero i (r : ren) :
    (E_var 0)[ᵣ i .ᵣ r] =σ E_var i
| aeq_rcons_succ i j (r : ren) :
    (E_var (S i))[ᵣ j .ᵣ r] =σ (E_var i)[ᵣ r]

(** Apply a substitution to a variable. *)

| aeq_sshift_var i k : 
    (E_var i)[ₛ ↑ₛ k ] =σ E_var (k + i)
| aeq_scons_zero (t : term) (s : subst) :
    (E_var 0)[ₛ t .ₛ s] =σ t
| aeq_scons_succ i (t : term) (s : subst) :
    (E_var (S i))[ₛ t .ₛ s] =σ (E_var i)[ₛ s]

(** Push a renaming/substitution inside an expression. *)

| aeq_inst_ctor {k} c (al : args _) (s : expr (K2 k)) : 
    (E_ctor c al)[: s ] =σ E_ctor c (al[: s ])
| aeq_inst_al_nil {k} (s : expr (K2 k)) : 
    E_al_nil[: s ] =σ E_al_nil
| aeq_inst_al_cons {k ty tys} (a : arg ty) (al : args tys) (s : expr (K2 k)) : 
    (E_al_cons a al)[: s ] =σ E_al_cons (a[: s]) (al[: s ])
| aeq_inst_abase {k} b x (s : expr (K2 k)) : 
    (E_abase b x)[: s ] =σ E_abase b x
| aeq_inst_aterm {k} (t : term) (s : expr (K2 k)) : 
    (E_aterm t)[: s ] =σ E_aterm (t[: s ])
| aeq_inst_abind_s {ty} (a : arg ty) (s : subst) : 
    (E_abind a)[ₛ s ] =σ E_abind (a[ₛ up_subst s ])
| aeq_inst_abind_r {ty} (a : arg ty) (r : ren) : 
    (E_abind a)[ᵣ r ] =σ E_abind (a[ᵣ up_ren r ])
| aeq_inst_inst {k k' k''} (e : expr (K1 k)) (s1 : expr (K2 k')) (s2 : expr (K2 k'')) :
    e[: s1 ][: s2 ] =σ e[: s1 >> s2 ]

(** Renaming laws. *)

| aeq_rshift_succ_r k : 
    ↑ᵣ k >> ↑ᵣ 1 =σ ↑ᵣ (S k)
| aeq_rshift_rcons :
    0 .ᵣ ↑ᵣ 1 =σ ↑ᵣ 0  
| aeq_rcons_rshift i (r : ren) :
    ↑ᵣ 1 >> (i .ᵣ r) =σ r
| aeq_rid_l (r : ren) : 
    rid >> r =σ r 
| aeq_rid_r (r : ren) : 
    r >> rid =σ r
| aeq_distrib_ren_subst i (r1 : ren) (s2 : subst) : 
    (i .ᵣ r1) >> s2 =σ (E_var i)[ₛ s2 ] .ₛ r1 >> s2
| aeq_rid_mvar {k} (v : denote_type (K1 k)) :
    (E_mvar v)[ᵣ rid ] =σ E_mvar v 

(** Substitution laws. *)

| aeq_sshift_succ_r k : 
    ↑ₛ k >> ↑ₛ 1 =σ ↑ₛ (S k)
| aeq_sshift_scons :
    E_var 0 .ₛ ↑ₛ 1 =σ ↑ₛ 0  
| aeq_scons_sshift (t : term) (s : subst) :
    ↑ₛ 1 >> (t .ₛ s) =σ s
| aeq_sid_l (s : subst) : 
    sid >> s =σ s 
| aeq_sid_r (s : subst) : 
    s >> sid =σ s
| aeq_distrib_subst {k} (t : term) (s1 : subst) (s2 : expr (K2 k)) : 
    (t .ₛ s1) >> s2 =σ t[: s2 ] .ₛ s1 >> s2
| aeq_sid_mvar {k} (v : denote_type (K1 k)) :
    (E_mvar v)[ₛ sid ] =σ E_mvar v 

(** Link between substitutions and renamings. *)

| aeq_ren_subst {k} (t : expr (K1 k)) (r : ren) :
    t [ᵣ r ] =σ t [ₛ r >> sid ]
| aeq_rshift_shift_l i : 
    ↑ᵣ i >> sid =σ ↑ₛ i 
| aeq_rshift_shift_r i : 
    sid >> ↑ᵣ i =σ ↑ₛ i 

| aeq_assoc {k k' k''} (s1 : expr (K2 k)) (s2 : expr (K2 k')) (s3 : expr (K2 k'')) : 
    s1 >> (s2 >> s3) =σ (s1 >> s2) >> s3

where "t1 '=σ' t2" := (axiom_eq t1 t2).
Hint Constructors axiom_eq : core.*)

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

(*#[global] Instance axiom_eq_equiv k : Equivalence (@axiom_eq k).
Proof. constructor ; eauto. Qed.

#[global] Instance e_ctor_proper c : Proper (axiom_eq ==> axiom_eq) (@E_ctor c).
Proof. intros ???. apply aeq_congr_ctor ; auto. Qed.

#[global] Instance e_al_cons_proper ty tys : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_al_cons ty tys).
Proof. intros ??????. apply aeq_congr_al_cons ; auto. Qed.

#[global] Instance e_aterm_proper : Proper (axiom_eq ==> axiom_eq) E_aterm.
Proof. intros ???. apply aeq_congr_aterm ; auto. Qed.

#[global] Instance e_abind_proper ty : Proper (axiom_eq ==> axiom_eq) (@E_abind ty).
Proof. intros ???. apply aeq_congr_abind ; auto. Qed.

#[global] Instance e_inst_proper k1 k2 : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_inst k1 k2).
Proof. intros ??????. apply aeq_congr_inst ; auto. Qed.

#[global] Instance e_scons_proper : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) E_scons.
Proof. intros ??????. apply aeq_congr_scons ; auto. Qed.

#[global] Instance e_comp_proper k1 k2 : Proper (axiom_eq ==> axiom_eq ==> axiom_eq) (@E_comp k1 k2).
Proof. intros ??????. apply aeq_congr_comp ; auto. Qed.*)

(*********************************************************************************)
(** *** Additional functions and properties. *)
(*********************************************************************************)

(*Lemma up_subst_sid : up_subst sid =σ sid.
Proof. unfold up_subst. rewrite aeq_sid_l. now rewrite aeq_sshift_scons. Qed.

Lemma up_ren_rid : up_ren rid =σ rid.
Proof. unfold up_ren. rewrite aeq_rid_l. now rewrite aeq_sshift_scons. Qed.


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
Qed.*)




End Make.