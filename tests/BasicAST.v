From Coq Require Import Utf8.

Definition level := nat.

Inductive mode := mKind | mType | mGhost | mProp.

Inductive cmode := cType | cProp.

(** Mark to inidicate the orgin of some terms in the target.

  They bear no influence whatsoever but basically allow us to have several
  distinct copies of the ctyval constructor.

**)

Inductive mark := Any | WasKind | WasType | WasGhost.