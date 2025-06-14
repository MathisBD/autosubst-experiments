(** This file defines fixed length vectors [vec T n], encoded using
    an indexed inductive type (as opposed to a list with a proof for the length). *)

From Coq Require Import Relations Morphisms.
From Equations Require Import Equations.
From Utils Require Import Fin.

(*********************************************************************************)
(** *** Vectors. *)
(*********************************************************************************)

(** [vec T n] is the type of vectors of length [n] with elements in [T].
    It uses the standard encoding for fixed length vecs. *)
Inductive vec (T : Type) : nat -> Type :=
| vnil : vec T 0 
| vcons n : T -> vec T n -> vec T (S n).
Arguments vnil {T}.
Arguments vcons {T n}.

Derive Signature NoConfusion NoConfusionHom for vec.

(** Notation for vectors, in scope [vec]. *)

Declare Scope vec_scope.
Bind Scope vec_scope with vec.
Delimit Scope vec_scope with vec.

Notation "[-  -]" := vnil : vec_scope. 
Notation "[-  x  -]" := (vcons x vnil) : vec_scope.
Notation "[-  x ; y ; .. ; z  -]" := (vcons x (vcons y .. (vcons z vnil) ..)) : vec_scope.

(*********************************************************************************)
(** *** Operations on vectors. *)
(*********************************************************************************)

(** [vec_init n f] creates the vector of length [n] with elements 
    [f 0], [f 1], [f 2], etc. *)
Equations vec_init {T} (n : nat) (f : fin n -> T) : vec T n :=
vec_init 0 _ := vnil ;
vec_init (S n) f := vcons (f finO) (vec_init n (fun i => f (finS i))).

(** [vec_nth xs i] looks up the [i]-th element of [xs]. Contrary to lists,
    this does not return an [option T] or require a default element in [T]. *)
Equations vec_nth {T n} (xs : vec T n) (i : fin n) : T :=
vec_nth (vcons x xs) finO     := x ;
vec_nth (vcons x xs) (finS i) := vec_nth xs i.

(** [vec_map f xs] maps function [f] over vector [xs]. *)
Equations vec_map {T U n} (f : T -> U) (xs : vec T n) : vec U n :=
vec_map f vnil := vnil ;
vec_map f (vcons x xs) := vcons (f x) (vec_map f xs). 

(** [vec_mapi f xs] maps function [f] over vector [xs].
    [f] has access to the index of the element as a [fin n].  *)
Equations vec_mapi {T U n} (f : fin n -> T -> U) (xs : vec T n) : vec U n :=
vec_mapi f vnil := vnil ;
vec_mapi f (vcons x xs) := vcons (f finO x) (vec_mapi (fun i => f (finS i)) xs). 

(** [vec_map2 f xs ys] maps the binary function [f] over vectors [xs] and [ys]. *)
Equations vec_map2 {T1 T2 U n} (f : T1 -> T2 -> U) (xs : vec T1 n) (ys : vec T2 n) : vec U n :=
vec_map2 f vnil vnil := vnil ;
vec_map2 f (vcons x xs) (vcons y ys) := vcons (f x y) (vec_map2 f xs ys). 

(*********************************************************************************)
(** *** Lemmas about vectors. *)
(*********************************************************************************)

Lemma vec_nth_mapi {n T U} (f : fin n -> T -> U) xs i :
  vec_nth (vec_mapi f xs) i = f i (vec_nth xs i).
Proof. funelim (vec_nth xs i) ; simp vec_mapi vec_nth. reflexivity. Qed.
#[export] Hint Rewrite @vec_nth_mapi : vec_nth.

Lemma vec_nth_map2 {n T1 T2 U} (f : T1 -> T2 -> U) xs ys (i : fin n) :
  vec_nth (vec_map2 f xs ys) i = f (vec_nth xs i) (vec_nth ys i).
Proof. 
funelim (vec_nth xs i) ; depelim ys ; simp vec_map2 vec_nth. reflexivity.
Qed.
#[export] Hint Rewrite @vec_nth_map2 : vec_nth.

Lemma vec_nth_init {n T} (f : fin n -> T) i :
  vec_nth (vec_init n f) i = f i.
Proof. 
funelim (vec_init n f) ; depelim i ; simp vec_nth. reflexivity.
Qed.
#[export] Hint Rewrite @vec_nth_init : vec_nth.   

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

Section VecEq.
  Context {T : Type} (R : relation T) (H : Equivalence R).

  (** Two vectors are equal according to [vec_eq R] if their elements are 
      equal according to [R]. *)
  Definition vec_eq {n} : relation (vec T n) :=
    fun xs ys =>
      forall i : fin n, R (vec_nth xs i) (vec_nth ys i). 

  #[export] Instance vec_eq_equiv n : Equivalence (@vec_eq n).
  Proof. 
  constructor.
  - intros xs i. reflexivity.
  - intros xs ys Hsym i. now symmetry.
  - intros xs ys zs H1 H2 i. etransitivity ; eauto.
  Qed. 

  Lemma vec_eq_vcons_inv {n} (x x' : T) (xs xs' : vec T n) :
    vec_eq (vcons x xs) (vcons x' xs') ->
    R x x' /\ vec_eq xs xs'.
  Proof. 
  intros H'. split.
  - specialize (H' finO). exact H'.
  - intros i. specialize (H' (finS i)). exact H'.
  Qed.

End VecEq. 

#[export] Instance vec_map_proper {T U n} (RT : relation T) (RU : relation U) : 
  Proper ((RT ==> RU) ==> vec_eq RT ==> vec_eq RU) (@vec_map T U n). 
Proof.
intros f f' Hf xs xs' Hxs i. 
induction i ; depelim xs ; depelim xs' ; simp vec_nth vec_map.
- apply Hf. now apply vec_eq_vcons_inv in Hxs.
- apply IHi. now apply vec_eq_vcons_inv in Hxs.
Qed.

#[export] Instance vec_mapi_proper {T U n} (RT : relation T) (RU : relation U) : 
  Proper ((eq ==> RT ==> RU) ==> vec_eq RT ==> vec_eq RU) (@vec_mapi T U n). 
Proof.
intros f f' Hf xs xs' Hxs i.
induction i ; depelim xs ; depelim xs'.
- simp vec_nth. apply Hf ; try reflexivity. now apply vec_eq_vcons_inv in Hxs.
- simp vec_nth. apply Hf.
  + reflexivity. 
  + now apply vec_eq_vcons_inv in Hxs.
Qed.

#[export] Instance vec_map2_proper {T1 T2 U n} 
  (RT1 : relation T1) (RT2 : relation T2) (RU : relation U) : 
  Proper ((RT1 ==> RT2 ==> RU) ==> vec_eq RT1 ==> vec_eq RT2 ==> vec_eq RU) 
    (@vec_map2 T1 T2 U n). 
Proof. 
intros f f' Hf xs xs' Hxs ys ys' Hys i.
induction i ; depelim xs ; depelim xs' ; depelim ys ; depelim ys' ; simp vec_nth vec_map2.
- apply Hf ; try reflexivity. 
  + now apply vec_eq_vcons_inv in Hxs.
  + now apply vec_eq_vcons_inv in Hys.
- apply Hf. 
  + now apply vec_eq_vcons_inv in Hxs.
  + now apply vec_eq_vcons_inv in Hys.
Qed.
