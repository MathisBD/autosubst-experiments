From Coq Require Export Nat List String Morphisms Relations Program.Equality.
Export ListNotations.

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Add some power to [auto]. *)
#[global] Hint Extern 5 => f_equal : core.
#[global] Hint Extern 5 => simpl : core.

(** Cons a term with a substitution. *)
Class Scons (t s1 s2 : Type) :=
{ gen_scons : t -> s1 -> s2 }.
Notation "t .: s" := (gen_scons t s) (at level 70, right associativity).

(** Left to right composition of substitutions. *)
Class Scomp (s1 s2 s3 : Type) :=
{ gen_scomp : s1 -> s2 -> s3 }.
Notation "s1 >> s2" := (gen_scomp s1 s2) (at level 50, left associativity).

(** Apply a substitution to a term. *)
Class Subst (t1 s t2 : Type) := 
{ gen_subst : t1 -> s -> t2 }.
Notation "t '[:' s ']'" := (gen_subst t s) (at level 40, s at level 0, no associativity).
 
(** [fin n] represents the finite set with [n] elements [0], [1], ..., [n-1]. *)
Inductive fin : nat -> Type :=
| (** [0] is in [fin n] whenever [n > 0]. *)
  fin_zero {n} : fin (S n)
| (** Injection from [fin n] to [fin (S n)], which maps [i] to [i+1]. *)
  fin_succ {n} : fin n -> fin (S n).

(** Mapping from [i] to [i + k]. *)
Fixpoint fin_weaken {n} (k : nat) (i : fin n) : fin (k + n) :=
  match k return fin (k + n) with 
  | 0 => i
  | S k => fin_succ (fin_weaken k i)
  end.