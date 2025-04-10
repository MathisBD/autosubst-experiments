From Coq Require Export Nat List String Morphisms Relations Program.Equality Lia.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
Export ListNotations.

(** Ltac2 is still missing many basic Ltac1 tactics. *)
#[export] Set Default Proof Mode "Classic".

(** Convenience tactics. *)
Ltac inv H := inversion H ; subst.
Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].
Ltac triv := try solve [ eauto | easy ].

(** Add some power to [auto]. *)
#[global] Hint Extern 5 => f_equal : core.
#[global] Hint Extern 5 => simpl : core.

(** Pointwise equality for functions. *)
Definition point_eq {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (point_eq f g) (at level 75).

(** [fin n] represents the finite set with [n] elements [0], [1], ..., [n-1]. *)
Inductive fin : nat -> Type :=
| (** [0] is in [fin n] whenever [n > 0]. *)
  fin_zero {n} : fin (S n)
| (** Injection from [fin n] to [fin (S n)], which maps [i] to [i+1]. *)
  fin_succ {n} : fin n -> fin (S n).

(** Mapping from [i] to [i + k]. *)
Equations fin_weaken {n} (k : nat) (i : fin n) : fin (k + n) :=
fin_weaken 0 i := i ;
fin_weaken (S k) i := fin_succ (fin_weaken k i).
