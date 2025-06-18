(** This file defines finite sets [fin n] which can be thought of
    as sets [{ 0, 1, 2, ..., n-1 }]. *)

From Equations Require Import Equations.
From Coq Require Import Bool.

(** Enable reducing constants defined using [Equations]. *)
Set Equations Transparent.

Set Universe Polymorphism.

(*********************************************************************************)
(** *** Finite sets. *)
(*********************************************************************************)

(** [fin n] represents the finite set with [n] elements [0], [1], ..., [n-1]. *)
Inductive fin : nat -> Type :=
| (** [0] is in [fin n] whenever [n > 0]. *)
  finO {n} : fin (S n)
| (** Injection from [fin n] to [fin (S n)], which maps [i] to [i+1]. *)
  finS {n} : fin n -> fin (S n).

Derive Signature NoConfusion NoConfusionHom for fin.

(*********************************************************************************)
(** *** Operations on finite sets. *)
(*********************************************************************************)

(** Coercion from [fin n] to [nat]. *)
Equations fin_to_nat {n} : fin n -> nat :=
fin_to_nat finO := 0 ;
fin_to_nat (finS i) := S (fin_to_nat i).

(** Boolean equality test on [fin n]. *)
Equations eqb_fin {n} : fin n -> fin n -> bool :=
eqb_fin finO finO := true ;
eqb_fin (finS i) (finS i') := eqb_fin i i' ;
eqb_fin _ _ := false.

Lemma eqb_fin_spec {n} (i i' : fin n) : reflect (i = i') (eqb_fin i i').
Proof.
funelim (eqb_fin i i').
- now left.
- right. intros H. depelim H.
- right. intros H. depelim H.
- destruct H ; subst.
  + now left.
  + right. intros H. apply n. now depelim H.
Qed.     

(** Decidable equality on [fin n]. *)
#[export] Instance fin_EqDec n : EqDec (fin n).
Proof. intros i i'. destruct (eqb_fin_spec i i') ; constructor ; assumption. Defined.
