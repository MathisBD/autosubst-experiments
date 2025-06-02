From Coq Require Import Utf8 List.
From GhostTT Require Import Util GAST BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping Univ.

Import ListNotations.

Open Scope subst_scope.

Set Default Goal Selector "!".

Notation "A ⇒[ i | j / mx | m ] B" :=
  (Pi i j m mx A (rshift ⋅ B))
  (at level 20, i, j, mx, m at next level, right associativity).

Notation top := (bot ⇒[ 0 | 0 / mProp | mProp ] bot).