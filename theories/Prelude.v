From Coq Require Export List String Morphisms Relations Lia.
From Ltac2 Require Import Ltac2.
Export ListNotations.

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Add some power to [auto]. *)
#[global] Hint Extern 5 => f_equal : core.
#[global] Hint Extern 5 => simpl : core.
#[global] Hint Extern 10 => lia : core.

(** Cons a term with a substitution. *)
Class Scons (term subst : Type) :=
{ gen_scons : term -> subst -> subst }.
Notation "t .: s" := (gen_scons t s) (at level 70, right associativity).

(** Right to left composition of substitutions: apply [s2] followed by [s1]. *)
Class Scomp (subst : Type) :=
{ gen_scomp : subst -> subst -> subst }.
Notation "s1 ∘ s2" := (gen_scomp s1 s2) (at level 50, left associativity).

(** Substitute with substitution [s] in term [t]. *)
Class Subst (term subst : Type) := 
{ gen_subst : term -> subst -> term }.
Notation "t '[:' s ']'" := (gen_subst t s) (at level 40, s at level 0, no associativity).
 
