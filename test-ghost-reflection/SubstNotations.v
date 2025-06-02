(** Notations for substitutions and renamings

  They replace those of Autosubst that are incompatible with list notation.

**)

From Coq Require Import Utf8 List.
From GhostTT Require Import GAST.
From Coq Require Import Setoid Morphisms Relation_Definitions.
Import ListNotations.

Declare Scope subst_scope.

Notation "a ⋅ x" :=
  (rename a x) (at level 20, right associativity) : subst_scope.

Notation "t <[ s ]" :=
  (substitute s t) (at level 10, right associativity) : subst_scope.

Notation "↑" := (sshift) : subst_scope.
Notation "s '..'" := (scons s sid) (at level 1, format "s ..") : subst_scope.
Notation "t .: s" := (scons t s) (at level 55, s at next level, right associativity) : subst_scope.
Notation "s1 >> s2" := (scomp s1 s2) (at level 50) : subst_scope.


Notation "'↑ᵣ'" := (rshift) : subst_scope.
Notation "r '..ᵣ'" := (rcons r sid) (at level 1, format "r ..ᵣ") : subst_scope.
Notation "i '.:ᵣ' r" := (rcons i r) (at level 55, r at next level, right associativity) : subst_scope.
Notation "r1 '>>ᵣ' r2" := (rcomp r1 r2) (at level 50) : subst_scope.



(*Ltac autosubst_unfold :=
  unfold Ren_cterm, upRen_cterm_cterm, Subst_cterm, VarInstance_cterm,
    upRen_cterm_cterm, Ren_term, Subst_term, VarInstance_term, upRen_term_term.

Ltac resubst :=
  rewrite ?renRen_cterm, ?renSubst_cterm, ?substRen_cterm, ?substSubst_cterm,
    ?renRen_term, ?renSubst_term, ?substRen_term, ?substSubst_term.

Ltac ssimpl :=
  asimpl ;
  autosubst_unfold ;
  asimpl ;
  repeat unfold_funcomp ;
  resubst ;
  asimpl ;
  repeat unfold_funcomp.*)