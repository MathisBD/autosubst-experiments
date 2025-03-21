From Coq Require Import String List Morphisms Relations Lia.
From Ltac2 Require Import Ltac2.
Import ListNotations.

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Add some power to [auto]. *)
Hint Extern 5 => f_equal : core.
Hint Extern 5 => simpl : core.
Hint Extern 10 => lia : core.

(** Argument types over a set of base types. *)
Inductive arg_ty {base} :=
| AT_base : base -> arg_ty
| AT_term : arg_ty
| AT_bind : arg_ty -> arg_ty.

(** Signatures for abstract terms. *)
Module Type Signature.
  (** The set of base types, 
      e.g. [Inductive base := Unit | Bool | Nat]. *)
  Parameter base : Type.
  (** The actual type that each base type represents,
      e.g. a mapping Nat => nat ; Bool => bool ; Unit => unit. *)
  Parameter base_type : base -> Type.
  
  (** The set of constructors. *)
  Parameter ctor : Type.
  (** The number and type of each constructor argument. *)
  Parameter ctor_type : ctor -> list (@arg_ty base). 
End Signature.

(*********************************************************************************)
(** *** Level One. *)
(*********************************************************************************)

Module LevelOne (Sig : Signature).
Export Sig.
Definition arg_ty := @arg_ty base.

Inductive sort := 
| T (* Term. *)
| A (a : arg_ty) (* Argument. *)
| AL (args : list arg_ty). (* Argument list. *)

Inductive term : sort -> Type :=
| (* A term variable. *)
  T_var : nat -> term T
| (* A term constructor, applied to a list of arguments. *)
  T_ctor : forall c, term (AL (ctor_type c)) -> term T
(** A list of arguments of type [tys]. *)
| AL_nil : term (AL [])
| AL_cons {ty tys} : term (A ty) -> term (AL tys) -> term (AL (ty :: tys))
(** A single argument of type [ty]. *)
| A_base : forall b, base_type b -> term (A (AT_base b))
| A_term : term T -> term (A AT_term)
| A_bind {ty} : term (A ty) -> term (A (AT_bind ty)).

(** [lift n t] adds [1] to the index of every variable in [t] with index 
    greater or equal to [n]. Typically one uses [lift 0 t]. *)
Fixpoint lift {so} (n : nat) (t : term so) : term so :=
  match t with 
  | T_var k => if Nat.ltb k n then T_var k else T_var (S k)
  | T_ctor c args => T_ctor c (lift n args)
  | AL_nil => AL_nil
  | AL_cons a args => AL_cons (lift n a) (lift n args)
  | A_base b x => A_base b x
  | A_term t => A_term (lift n t)
  | A_bind t => A_bind (lift (S n) t)
  end.

(** The identity substitution. *)
Definition sid (n : nat) : term T := T_var n.

(** [sshift k] shifts indices by [k]. *)
Definition sshift (k : nat) (n : nat) : term T := T_var (n + k).

(** Cons a term with a substitution. *)
Definition scons (t : term T) (s : nat -> term T) (n : nat) : term T :=
  match n with 
  | 0 => t
  | S n => s n
  end.

(** Lift a substitution through a binder. *)
Definition up_subst (s : nat -> term T) : nat -> term T :=
  scons (T_var 0) (fun n => lift 0 (s n)).

(** Apply a substitution to a term. *)
Fixpoint subst {so} (t : term so) (s : nat -> term T) :=
  match t with 
  | T_var n => s n
  | T_ctor c args => T_ctor c (subst args s)
  | AL_nil => AL_nil
  | AL_cons a args => AL_cons (subst a s) (subst args s)
  | A_base b x => A_base b x
  | A_term t => A_term (subst t s)
  | A_bind a => A_bind (subst a (up_subst s))
  end.

(** [scomp s2 s1] applies substitution [s1] followed by [s2]. *)
Definition scomp (s2 s1 : nat -> term T) (n : nat) : term T :=
  subst (s1 n) s2.

End LevelOne.

(*********************************************************************************)
(** *** Level Two. *)
(*********************************************************************************)

Module LevelTwo (Sig : Signature).
Export Sig.
Definition arg_ty := @arg_ty base.

Inductive sort := 
| S (* Substitution. *)
| T (* Term. *)
| A (a : arg_ty) (* Argument. *) 
| AL (args : list arg_ty). (* Argument list. *)

(** Terms from the sigma calculus. Terms are well-formed by construction,
    i.e. we enforce that constructors are applied to the right number 
    and types of arguments _intrinsically_ instead of _extrinsically_. *)
Inductive term : sort -> Type :=
| (* A term variable. *)
  T_var : nat -> term T
| (* A term constructor, applied to a list of arguments. *)
  T_ctor : forall c, term (AL (ctor_type c)) -> term T
| (* An explicit substitution, applied to a term. *)
  T_subst : term T -> term S -> term T
(** A list of arguments of type [tys]. *)
| AL_nil : term (AL [])
| AL_cons {ty tys} : term (A ty) -> term (AL tys) -> term (AL (ty :: tys))
| AL_subst {tys} : term (AL tys) -> term S -> term (AL tys)
(** A single argument of type [ty]. *)
| A_base : forall b, base_type b -> term (A (AT_base b))
| A_term : term T -> term (A AT_term)
| A_bind {ty} : term (A ty) -> term (A (AT_bind ty))
| A_subst {ty} : term (A ty) -> term S -> term (A ty)
(** Explicit substitutions. *)
| (* [S_shift k] maps [n] to [n+k]. *)
  S_shift : nat -> term S
| (* [S_cons t s] or [t .: s] maps [0] to [t] and [n+1] to [s n]. *)
  S_cons : term T -> term S -> term S
| (* [S_comp s1 s2] or [s1 ∘ s2] applies [s2] followed by [s1].
     Notice the right to left evaluation order (as usual with composition). *)
  S_comp : term S -> term S -> term S
| (* Substitution metavariables. *)
  S_mvar : nat -> term S.

(* Custom notations to ease writing terms and substitutions. *)
Notation "t .: s" := (S_cons t s) (at level 70, right associativity).
Notation "s1 ∘ s2" := (S_comp s1 s2) (at level 50, left associativity).

Class Subst (X : Type) := { subst : X -> term S -> X }.
Instance t_subst : Subst (term T) := { subst := T_subst }.
Instance a_subst ty : Subst (term (A ty)) := { subst := A_subst }.
Instance al_subst tys : Subst (term (AL tys)) := { subst := AL_subst }.
Notation "t '[:' s ']'" := (subst t s) (at level 40, s at level 0, no associativity).

(** The identity substitution. *)
Definition S_id : term S := S_shift 0.

(** Apply a substitution to an index. *)
Fixpoint apply_subst (s : term S) (n : nat) : term T :=
  match n, s with 
  | n, S_shift k => T_var (n + k)
  | 0, t .: s => t
  | Datatypes.S n, t .: s => apply_subst s n
  | n, s2 ∘ s1 => (apply_subst s1 n)[: s2]
  | _, _ => T_subst (T_var n) s
  end.

(** [t σ= t'] means that the terms/substitutions [t] and [t'] are equal 
    modulo the equational theory of sigma calculus. *)
Reserved Notation "t1 '=σ' t2" (at level 75, no associativity).
Inductive seq : forall s, term s -> term s -> Prop :=

(** Equivalence. *)

| seq_refl s (t : term s) : t =σ t
| seq_sym s (t1 t2 : term s) : t1 =σ t2 -> t2 =σ t1
| seq_trans s (t1 t2 t3 : term s) : t1 =σ t2 -> t2 =σ t3 -> t1 =σ t3

(** Congruence. *)

| seq_t_ctor c args1 args2 : 
    args1 =σ args2 -> T_ctor c args1 =σ T_ctor c args2
| seq_t_subst (t1 t2 : term T) s1 s2 : 
    t1 =σ t2 -> s1 =σ s2 -> t1[: s1 ] =σ t2[: s2 ] 

| seq_al_cons ty tys (a1 a2 : term (A ty)) (args1 args2 : term (AL tys)) : 
    a1 =σ a2 -> args1 =σ args2 -> AL_cons a1 args1 =σ AL_cons a2 args2
| seq_al_subst tys (args1 args2 : term (AL tys)) s1 s2 :
    args1 =σ args2 -> s1 =σ s2 -> args1[: s1] =σ args2[: s2]

| seq_a_term t1 t2 : t1 =σ t2 -> A_term t1 =σ A_term t2
| seq_a_bind ty (a1 a2 : term (A ty)) : a1 =σ a2 -> A_bind a1 =σ A_bind a2
| seq_a_subst ty (a1 a2 : term (A ty)) s1 s2 :
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
| seq_distrib t s1 s2 : s2 ∘ (t .: s1) =σ t[: s2 ] .: s2 ∘ s1

where "t1 '=σ' t2" := (seq _ t1 t2).
Hint Constructors seq  : core.

(** *** Setoid rewrite support. *)

Instance seq_equiv s : Equivalence (seq s).
Proof. constructor ; eauto. Qed.

Instance t_subst_proper : Proper (seq T ==> seq S ==> seq T) T_subst.
Proof. intros ? ? ? ? ? ?. auto. Qed.

(* TODO : other instances. *)
    
(** Simplify a term/substitution. *)
Definition simpl {so} (t : term so) : term so :=
  match t in term so0 return term so0 with 
  | T_subst t' s' => 
    match s' with 
    | T_var 0 .: S_shift 1 => t'
    | _ => t' [: s']
    end
  | t' => t'
  end.

Lemma simpl_sound {so} (t : term so) : simpl t =σ t.
Proof.
destruct t ; simpl ; try (now eauto).
(* TODO *)
Admitted.

End LevelTwo.

(*********************************************************************************)
(** *** Level One <-> Level Two. *)
(*********************************************************************************)

Module MappingOneTwo (Sig : Signature).
Module One := LevelOne (Sig).
Module Two := LevelTwo (Sig). 
Import Sig One.
  
Ltac2 rec nat_of_int (n : int) : constr :=
  if Int.lt 0 n then 
    let n' := nat_of_int (Int.sub n 1) in
    constr:(S $n')
  else 
    constr:(0).

(** Mapping from level one terms/substitutions to 
    level two terms/substitutions + environments (lists of level one substitutions). *)
Ltac2 rec reify (env : constr list) (t : constr) : constr list * constr :=
  lazy_match! t with 
  (* Terms constructors. *)
  | T_var ?n => (env, constr:(Two.T_var $n))
  | T_ctor ?c ?args => 
    let (env, args') := reify env args in
    (env, constr:(Two.T_ctor $c $args'))
  | AL_nil => (env, constr:(Two.AL_nil))
  | AL_cons ?a ?args =>
    let (env, a') := reify env a in
    let (env, args') := reify env args in
    (env, constr:(Two.AL_cons $a' $args'))
  | A_base ?b ?x => (env, constr:(Two.A_base $b $x))
  | A_term ?t => 
    let (env, t') := reify env t in
    (env, constr:(Two.A_term $t')) 
  | A_bind ?a =>
    let (env, a') := reify env a in
    (env, constr:(Two.A_bind $a'))
  (* Substitution applied to a term. *)
  | @subst AL ?args ?s =>
    let (env, args') := reify env args in 
    let (env, s') := reify_subst env s in
    (env, constr:(Two.AL_subst $args' $s'))
  | @subst A ?t ?s =>
    let (env, t') := reify env t in
    let (env, s') := reify_subst env s in
    (env, constr:(Two.A_subst $t' $s'))
  | @subst T ?t ?s =>
    let (env, t') := reify env t in
    let (env, s') := reify_subst env s in
    (env, constr:(Two.T_subst $t' $s'))
  (* Unkown term. *)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "reify: term mvars not handled yet")))
  end
with reify_subst (env : constr list) (s : constr) : constr list * constr :=
  lazy_match! s with 
  (* Usual substitutions. *)
  | sid => (env, constr:(Two.S_id))
  | sshift ?k => (env, constr:(Two.S_shift $k))
  | scons ?t ?s => 
    let (env, t') := reify env t in 
    let (env, s') := reify_subst env s in 
    (env, constr:(Two.S_cons $t' $s'))
  | scomp ?s1 ?s2 =>
    let (env, s1') := reify_subst env s1 in
    let (env, s2') := reify_subst env s2 in
    (env, constr:(Two.S_comp $s1' $s2'))
  (* Unkown substitutions. *)
  | _ => 
    let n := nat_of_int (List.length env) in
    (s :: env, constr:(Two.S_mvar $n))
  end.

Ltac2 Eval reify [] constr:(subst (T_var 3) (scons (T_var 1) (scomp sid (fun n => T_var (2+n))))).

Definition denote_sort (s : Two.sort) : Type :=
  match s with 
  | Two.S => nat -> term T
  | Two.T => term T
  | Two.AL tys => term (AL tys)
  | Two.A ty => term (A ty)
  end.

(*Section Denote.
  Context (env : list (denote_sort Two.S)).

  Fixpoint lookup_env 

  (** Mapping from level two terms/substitutions to level one terms/substitutions. *)
  Fixpoint denote {s : Two.sort} (t : Two.term s) : denote_sort s :=
    match t in Two.term s0 return denote_sort s0  with
    | Two.S_shift k => sshift k
    | Two.S_cons t s => scons (denote t) (denote s)
    | Two.S_comp s1 s2 => scomp (denote s1) (denote s2)
    | Two.S_mvar n => lookup_env n

    | Two.T_var n => T_var n 
    | Two.T_ctor c args => T_ctor c (denote args)
    | Two.T_subst t s => subst (denote t) (denote s)
    
    | Two.AL_nil => AL_nil
    | Two.AL_cons a args => AL_cons (denote a) (denote args)
    | Two.AL_subst args s => subst (denote args) (denote s)
  
    | Two.A_base b x => A_base b x
    | Two.A_term t => A_term (denote t)
    | Two.A_bind a => A_bind (denote a)
    | Two.A_subst a s => subst (denote a) (denote s)
    end.

(** Equality on level one terms/substitutions. 
    We only consider pointwise equality for substitutions, so as to not assume 
    functional extensionality. *)
Definition one_eq (so : Two.sort) : relation (denote_sort so) :=
  match so with 
  | Two.S => pointwise_relation _ eq
  | _ => eq
  end.

Instance one_eq_equiv so : Equivalence (one_eq so).
Proof.
destruct so ; constructor ; simpl ; try (now eauto).
all: (intros ? ? ? ? ? ; etransitivity ; now eauto).
Qed.

Instance subst_proper so : Proper (eq ==> pointwise_relation _ eq ==> eq) (@subst so).
Proof. 
intros t ? <-. induction t ; intros s1 s2 Hs ; simpl ; try (now auto).
f_equal. apply IHt. intros [|n] ; auto.
Qed. 

Lemma subst_id so (t : term so) : subst t sid = t.
Proof.
induction t ; try (now auto).
simpl. f_equal. rewrite <-IHt at 2. apply subst_proper.
- reflexivity.
- intros [|n] ; auto.
Qed.

Lemma lift_subst so (t : term so) k : 
  lift k t = subst t (fun n => if Nat.ltb n k then T_var n else T_var (S n)).
Proof.
revert k. induction t ; intros k ; simpl ; try (now auto).
f_equal. rewrite IHt. apply subst_proper ; auto.
intros [|n] ; simpl ; auto.
destruct (PeanoNat.Nat.ltb_spec n k) ; destruct (PeanoNat.Nat.ltb_spec (S n) (S k)) ; 
simpl ; solve [ ltac1:(lia) | reflexivity ].
Qed.

Lemma subst_comp so (t : term so) s1 s2 : subst (subst t s1) s2 = subst t (scomp s2 s1).
Proof.
revert s1 s2. induction t ; intros s1 s2 ; simpl ; try (now auto).
f_equal. rewrite IHt. apply subst_proper ; auto.
intros n. cbv [scomp]. destruct n as [|n] ; simpl ; auto.
generalize (s1 n) ; intros t'.
Admitted.

Instance denote_proper so : Proper (Two.seq so ==> one_eq so) denote.
Proof.
intros t1 t2 Ht. induction Ht ; simpl in * ; try (now auto).
- etransitivity ; eauto.
- now rewrite IHHt1, IHHt2.
- now rewrite IHHt1, IHHt2.
- now rewrite IHHt1, IHHt2. 
- intros [|n] ; auto.
- intros [|n] ; cbv [scomp] ; now rewrite IHHt1, IHHt2.
- admit.
- f_equal. apply subst_proper ; auto.
  intros [|n] ; simpl ; auto. cbv [scomp]. rewrite lift_subst.
  apply subst_proper ; auto. intros [|] ; auto. simpl. cbv [sshift]. f_equal.
  ltac1:(lia).
- intros n. cbv [scomp]. simpl. cbv [sshift]. auto.  
- intros n. cbv [scomp]. rewrite <- subst_id. apply subst_proper ; auto.
  intros [|n'] ; auto. cbv [sshift]. auto. 
- intros n. cbv [scomp]. destruct n as [|n] ; auto.
- intros n. cbv [scomp]. rewrite subst_comp. reflexivity.
- intros n. cbv [scomp]. destruct n as [|n] ; auto.    
Admitted.   

(*Lemma test : one_eq Two.T (T_var 0) (subst (T_var 3) (scons (T_var 0) (sshift 1))).
Proof.
let t2 := reify constr:(subst (T_var 3) (scons (T_var 0) (sshift 1))) in
let t1 := constr:(one_eq Two.T (T_var 0) (denote $t2)) in
change $t1 ;
rewrite <-(Two.simpl_sound $t2).
cbn [Two.simpl].
simpl.
Admitted.*)

End MappingOneTwo.

(** *** Example : lambda calculus. *)

(** Concrete terms. 
    Applications carry a boolean.
    Lambda abstractions contain the name of the bound variable as a string. *)
Inductive cterm :=
  | Var : nat -> cterm
  | App : bool -> cterm -> cterm -> cterm
  | Lam : string -> cterm -> cterm.

(** Basic substitutions. *)
Definition cid (n : nat) : cterm := Var n.
Definition cshift (n : nat) : cterm := Var (S n).
Definition ccons (t : cterm) (s : nat -> cterm) (n : nat) : cterm :=
  match n with 
  | 0 => t
  | S n => s n
  end.

Fixpoint lift k (t : cterm) : cterm :=
  match t with 
  | Var n => if Nat.ltb n k then Var n else Var (S n)
  | App b t1 t2 => App b (lift k t1) (lift k t2)
  | Lam str t => Lam str (lift (S k) t)
  end.

(** Concrete substitution function. *)
Fixpoint csubst (t : cterm) (s : nat -> cterm) {struct t} : cterm :=
  match t with 
  | Var n => s n
  | App b t1 t2 => App b (csubst t1 s) (csubst t2 s)
  | Lam str t => 
    let s := ccons (Var 0) (fun n => lift 0 (s n)) in
    Lam str (csubst t s)
  end.

Definition ccomp (s1 : nat -> cterm) (s2 : nat -> cterm) (n : nat) : cterm :=
  csubst (s2 n) s1.

(*Instance csubst_proper : Proper (eq ==> pointwise_relation nat eq ==> eq) csubst.
Proof.
intros t ? <-. induction t ; intros s1 s2 Hs ; simpl.
- auto.
- f_equal ; auto.
- f_equal. apply IHt. intros [|n] ; simpl.
  + reflexivity.
  + now rewrite Hs.
Qed.  

Lemma cshift_cid : pointwise_relation _ eq (ccons (Var 0) cshift) cid.
Proof. intros [|] ; reflexivity. Qed.

Lemma csubst_cid t : csubst t cid = t.
Proof.
induction t ; simpl.
- reflexivity.
- now rewrite IHt1, IHt2.
- now rewrite cshift_cid, IHt.
Qed.  *)

(** Abstract signature. *)

Module Sig.
  Inductive base_ := BString | BBool.
  Definition base := base_.
  
  Definition base_type (b : base) : Type :=
    match b with BString => string | BBool => bool end.
  
  Inductive ctor_ := CApp | CLam. 
  Definition ctor := ctor_. 

  Definition ctor_type (c : ctor) : list arg_ty :=
    match c with 
    | CApp => [ AT_base BBool ; AT_term ; AT_term ]
    | CLam => [ AT_base BString ; AT_bind (AT_term) ]
    end.
End Sig.

(** Abstract terms. *)
Module One := LevelOne (Sig).
Import One.

(** Mapping from level one terms/substitutions to level two terms/substitutions. *)
Ltac2 rec reify (t : constr) : constr :=
  lazy_match! t with 
  (* Terms constructors. *)
  | Var ?n => constr:(T_var $n)
  | App ?b ?t1 ?t2 => 
    let b' := constr:(A_base BBool $b) in
    let t1' := reify t1 in
    let t2' := reify t2 in
    constr:(T_ctor CApp 
      (AL_cons $b' (AL_cons (A_term $t1') (AL_cons (A_term $t2') AL_nil))))
  | Lam ?str ?t =>
    let str' := constr:(A_base BString $str) in
    let t' := reify t in
    constr:(T_ctor CLam
      (AL_cons $str' (AL_cons (A_bind (A_term $t')) AL_nil)))
  (* Substitution applied to a term. *)
  | @csubst ?t ?s =>
    let t' := reify t in 
    let s' := reify_subst s in
    constr:(@subst T $t' $s')
  (* Unkown term. *)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "reify(concrete): unkown case")))
  end
with reify_subst (s : constr) : constr :=
  lazy_match! s with 
  (* Usual substitutions. *)
  | cid => constr:(sid)
  | cshift => constr:(sshift)
  | ccons ?t ?s => 
    let t' := reify t in 
    let s' := reify_subst s in 
    constr:(scons $t' $s')
  | ccomp ?s1 ?s2 =>
    let s1' := reify_subst s1 in
    let s2' := reify_subst s2 in
    constr:(scomp $s1' $s2')
  (* Unkown substitution. *)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "reify: unkown case")))
  end.


(**************)
Section DenoteSort.
  (* Denotation for [term]. *)
  Context (denote_term : Type).

  (** Denote argument types into [Type]. *)
  Fixpoint denote_arg_ty (ty : arg_ty) : Type :=
    match ty with 
    | AT_base b => base_type b
    | AT_term => denote_term
    | AT_bind ty => denote_arg_ty ty
    end.

  (** Denote the type of a term constructor with arguments in [tys].
      We build the (non-dependent) arrow [ty0 -> ty1 -> ... -> term]. *)
  Fixpoint denote_al_ty (tys : list arg_ty) : Type :=
    match tys with 
    | [] => denote_term
    | ty :: tys => denote_arg_ty ty -> denote_al_ty tys
    end.

  Definition denote_sort (s : sort) : Type :=
    match s with 
    | T => denote_term
    | AL tys => denote_al_ty tys -> denote_term
    | A ty => denote_arg_ty ty
    end.
End DenoteSort.
(**************)

Definition denote_ctor (c : ctor) : denote_al_ty cterm (ctor_type c) :=
  match c with 
  | CApp => App
  | CLam => Lam
  end.

(** Mapping from abstract terms to concrete terms. 
    This uses some continuation passing style (when denoting argument lists). *)
Fixpoint denote {s} (t : One.term s) : denote_sort cterm s :=
  match t with
  | T_var n => Var n 
  | T_ctor c args => (denote args) (denote_ctor c)
  | AL_nil => fun t => t
  | AL_cons a args => fun f => (denote args) (f (denote a))
  | A_base b x => x
  | A_term t => denote t
  | A_bind a => denote a
  end.

Lemma csubst_spec (t : cterm) (s : nat -> cterm) : 
  csubst t s = denote (T_subst (reify t) (fun n => reify (s n))).

Definition sort_rel (s : sort) : relation (denote_sort cterm s) :=
  match s with 
  | S => pointwise_relation _ eq
  | T => eq
  | A ty => eq
  | AL tys => pointwise_relation _ eq
  end.

Instance sort_rel_equiv s : Equivalence (sort_rel s).
Proof.
destruct s ; simpl ; constructor ; auto.
all: intros ? ; etransitivity ; now eauto.
Qed.

Lemma csubst_comp t s1 s2 : csubst (csubst t s1) s2 = csubst t (ccomp s2 s1).
Proof.
induction t ; simpl ; cbv [ccomp].
- reflexivity.
- now rewrite IHt1, IHt2.
- f_equal. admit.
Admitted.

Lemma denote_sound {s} : Proper (seq s ==> sort_rel s) denote.
Proof.
intros t1 t2 Ht. induction Ht ; simpl in * ; try now auto.
- etransitivity ; eauto.
- now rewrite IHHt1, IHHt2.
- rewrite IHHt1. intros f. auto.
- intros [|n] ; simpl ; auto.
- intros n ; cbv [ccomp]. now rewrite IHHt1, IHHt2.
- admit. (* TODO : push subst. *) 
- intros n ; cbv [ccomp]. now rewrite cshift_cid, csubst_cid.
- intros n ; cbv [ccomp]. now rewrite cshift_cid.
- intros n ; cbv [ccomp]. now rewrite csubst_comp.
- intros n ; cbv [ccomp]. 

(*with denote_args {tys} (hd : denote_ctor_ty cterm tys) (args : arg_list tys) : cterm :=
  match args, hd with 
  | ANil, hd => hd
  | ACons a args, hd => denote_args (hd (denote_arg a)) args
  end
with denote_arg {ty} (a : arg ty) : denote_arg_ty cterm ty :=
  match a in arg ty0 return denote_arg_ty cterm ty0 with 
  | ABase b x => x
  | AVar n => n
  | ATerm t => denote t
  | ABind a' => denote_arg a'
  end.*)*)

  
End MappingOneTwo.
