From Equations Require Export Equations.

Inductive fin : nat -> Type :=
| finO {n} : fin (S n)
| finS {n} : fin n -> fin (S n).

Inductive term {nsort : nat} : fin nsort -> Type :=
| T_var {s} : term s.

Equations eval_sort (s : fin 1) : Type :=
eval_sort finO := unit.

Equations eval {s1} : @term 1 s1 -> eval_sort s1 :=
eval (@T_var _ finO) := tt.