From Coq Require Import Relations Morphisms.
From Equations Require Import Equations.
From Utils Require Import Fin Vector.

(*********************************************************************************)
(** *** Heterogeneous vectors. *)
(*********************************************************************************)

(** [hvec n T] is the type of vectors of length [n] with the [i]-th element
    of type [T i]. Note that we use a function [fin n -> Type] to give the types
    of the elements, instead of the standard encoding using a vector 
    [vector n A] and a function [A -> Type]. *)
Inductive hvec : forall n, (fin n -> Type) -> Type :=
| hnil {T} : hvec 0 T
| hcons {n T} : T finO -> hvec n (fun i => T (finS i)) -> hvec (S n) T.

Derive Signature NoConfusion NoConfusionHom for hvec.

(** Notations for heterogeneous vectors, in scope [hvec]. *)

Declare Scope hvec_scope.
Bind Scope hvec_scope with hvec.
Delimit Scope hvec_scope with hvec.

Notation "[=  =]" := hnil : hvec_scope.
Notation "[=  x  =]" := (hcons x hnil) : hvec_scope.
Notation "[=  x ; y ; .. ; z  =]" := (hcons x (hcons y .. (hcons z hnil) ..)) : hvec_scope.

(*********************************************************************************)
(** *** Operations on heterogeneous vectors. *)
(*********************************************************************************)

(** Convert a homogeneous vector into a heterogeneous vector. *)
Equations hvec_of_vec {n T} (xs : vec T n) : hvec n (fun _ => T) :=
hvec_of_vec vnil := hnil ;
hvec_of_vec (vcons x xs) := hcons x (hvec_of_vec xs).

(** [hvec_init n f] creates the heterogeneous vector of length [n] with elements 
    [f 0], [f 1], [f 2], etc. *)
Equations hvec_init (n : nat) {T : fin n -> Type} (f : forall i, T i) : hvec n T :=
hvec_init 0 _ := hnil ;
hvec_init (S n) f := hcons (f finO) (hvec_init n (fun i => f (finS i))).

(** [hvec_nth xs i] looks up the [i]-th element of [xs], which has type [T i]. *)
Equations hvec_nth {n T} (h : hvec n T) (i : fin n) : T i :=
hvec_nth (hcons x xs) finO     := x ;
hvec_nth (hcons x xs) (finS i) := hvec_nth xs i.

(** [hvec_mapi f xs] maps function [f] over vector [xs]. 
    [f] has access to the index of the element as a [fin n]. *)
Equations hvec_mapi {n T U} (f : forall i, T i -> U i) (xs : hvec n T) : hvec n U :=
hvec_mapi f hnil := hnil ;
hvec_mapi f (hcons x xs) := hcons (f finO x) (hvec_mapi (fun i => f (finS i)) xs).

(** [hvec_mapi2 f xs ys] maps the binary function [f] over heterogeneous vectors [xs] and [ys]. *)
Equations hvec_mapi2 {n T1 T2 U} (f : forall i, T1 i -> T2 i -> U i) 
  (xs : hvec n T1) (ys : hvec n T2) : hvec n U :=
hvec_mapi2 f hnil hnil := hnil ;
hvec_mapi2 f (hcons x xs) (hcons y ys) := 
  hcons (f finO x y) (hvec_mapi2 (fun i => f (finS i)) xs ys). 

(*********************************************************************************)
(** *** Lemmas about heterogeneous vectors. *)
(*********************************************************************************)

Lemma hvec_nth_vec {n T} (xs : vec T n) i :
  hvec_nth (hvec_of_vec xs) i = vec_nth xs i.
Proof.
funelim (hvec_of_vec xs).
- depelim i.
- depelim i ; simp vec_nth hvec_nth. reflexivity.
Qed.
#[export] Hint Rewrite @hvec_nth_vec : hvec_nth.

Lemma hvec_nth_init {n} {T : fin n -> Type} (f : forall i, T i) (i0 : fin n) :
  hvec_nth (hvec_init n f) i0 = f i0.
Proof. 
induction n in T, f, i0 |- * ; simp hvec_init.
- depelim i0.
- depelim i0.
  + simp hvec_nth. reflexivity. 
  + simp hvec_nth. apply (IHn (fun i => T (finS i))).
Qed.   
#[export] Hint Rewrite @hvec_nth_init : hvec_nth.   

Lemma hvec_nth_mapi {n} {T U : fin n -> Type} (f : forall i, T i -> U i) xs i :
  hvec_nth (hvec_mapi f xs) i = f i (hvec_nth xs i).
Proof. 
induction n in T, U, f, xs, i |- *.
- depelim i.
- depelim i ; depelim xs ; simp hvec_nth hvec_mapi.
  + reflexivity.
  + apply (IHn (fun i => T (finS i)) (fun i => U (finS i))).
Qed.
#[export] Hint Rewrite @hvec_nth_mapi : hvec_nth.

Lemma hvec_nth_mapi2 {n} {T1 T2 U : fin n -> Type} (f : forall i, T1 i -> T2 i -> U i) xs ys i :
  hvec_nth (hvec_mapi2 f xs ys) i = f i (hvec_nth xs i) (hvec_nth ys i).
Proof. 
induction n in T1, T2, U, f, xs, ys, i |- *.
- depelim i.
- depelim i ; depelim xs ; depelim ys ; simp hvec_nth hvec_mapi2.
  + reflexivity.
  + apply (IHn (fun i => T1 (finS i)) (fun i => T2 (finS i)) (fun i => U (finS i))).
Qed.
#[export] Hint Rewrite @hvec_nth_mapi2 : hvec_nth.

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

(** Equality on heterogeneous vectors. *)
Section HvecEq.
  Context {n : nat} {T : fin n -> Type} (eq : forall i, relation (T i)) 
    (H : forall i, Equivalence (eq i)).

  (** Two heterogeneous vectors are equal according to [hvec_eq R] if their 
      elements are equal according to [R]. *)
  Definition hvec_eq : relation (hvec n T) :=
    fun xs ys =>
      forall i : fin n, eq i (hvec_nth xs i) (hvec_nth ys i). 

  #[export] Instance hvec_eq_equiv : Equivalence hvec_eq.
  Proof. 
  constructor.
  - intros xs i. reflexivity.
  - intros xs ys Hsym i. now symmetry.
  - intros xs ys zs H1 H2 i. etransitivity ; eauto.
  Qed. 

End HvecEq.

#[export] Instance hvec_of_vec_proper {n T} (R : relation T) : 
  Proper (vec_eq R ==> hvec_eq (fun _ => R)) (@hvec_of_vec n T).
Proof. intros xs xs' H i. rewrite !hvec_nth_vec. apply H. Qed.

#[export] Instance hvec_mapi_proper {n} {T U : fin n -> Type} 
  (RT : forall i, relation (T i)) (RU : forall i, relation (U i)) : 
  let R : relation (forall i, T i -> U i) :=
    fun f f' =>
      forall i,
      forall (x x' : T i), RT i x x' ->
      RU i (f i x) (f' i x') 
  in
  Proper (R ==> hvec_eq RT ==> hvec_eq RU) 
    (@hvec_mapi n T U). 
Proof.
cbn. induction n in T, U, RT, RU |- * ; intros f f' Hf xs xs' Hxs i ; depelim i.
all: depelim xs ; depelim xs' ; simp hvec_nth ; apply Hf ; apply Hxs.
Qed.   

#[export] Instance hvec_mapi2_proper {n} {T1 T2 U : fin n -> Type} 
  (RT1 : forall i, relation (T1 i)) (RT2 : forall i, relation (T2 i)) (RU : forall i, relation (U i)) : 
  let Rf : relation (forall i, T1 i -> T2 i -> U i) :=
    fun f f' =>
      forall i,
      forall (x x' : T1 i), RT1 i x x' ->
      forall (y y' : T2 i), RT2 i y y' ->
      RU i (f i x y) (f' i x' y') 
  in
  Proper (Rf ==> hvec_eq RT1 ==> hvec_eq RT2 ==> hvec_eq RU) 
    (@hvec_mapi2 n T1 T2 U). 
Proof.
cbn. induction n in T1, T2, U, RT1, RT2, RU |- * ; intros f f' Hf xs xs' Hxs ys ys' Hys i ; depelim i.
all: depelim xs ; depelim xs' ; depelim ys ; depelim ys' ; simp hvec_nth.
all: apply Hf ; solve [ apply Hxs | apply Hys ].
Qed. 
