From Coq Require Import Utf8 List.
From GhostTT Require Import Util GAST BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping.

Import ListNotations.

Set Default Goal Selector "!".

(*** Equality of universe levels **)
Definition ueq (m : mode) (i j : level) :=
  m = mProp ∨ i = j.

Lemma ueq_eq :
  ∀ m i j,
    isProp m = false →
    ueq m i j →
    i = j.
Proof.
  intros m i j hm [-> | ->]. 1: discriminate.
  reflexivity.
Qed.

Lemma ueq_Kind_eq :
  ∀ i j,
    ueq mKind i j →
    i = j.
Proof.
  intros i j e.
  eapply ueq_eq. 2: eassumption.
  reflexivity.
Qed.

Lemma ueq_Type_eq :
  ∀ i j,
    ueq mType i j →
    i = j.
Proof.
  intros i j e.
  eapply ueq_eq. 2: eassumption.
  reflexivity.
Qed.

Lemma ueq_Ghost_eq :
  ∀ i j,
    ueq mGhost i j →
    i = j.
Proof.
  intros i j e.
  eapply ueq_eq. 2: eassumption.
  reflexivity.
Qed.

Ltac ueq_subst :=
  repeat lazymatch goal with
  | e : ueq mKind ?i ?j |- _ => eapply ueq_Kind_eq in e ; try subst i
  | e : ueq mType ?i ?j |- _ => eapply ueq_Type_eq in e ; try subst i
  | e : ueq mGhost ?i ?j |- _ => eapply ueq_Ghost_eq in e ; try subst i
  end.

(** Successor of a universe **)
Definition usup m i :=
  if isProp m then 0 else S i.

(** Maximum of a universe **)
Definition umax mx m i j :=
  if isProp m then 0
  else if isProp mx then j
  else max i j.