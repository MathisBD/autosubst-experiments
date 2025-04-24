Declare ML Module "autosubst-experiments.plugin".

Inductive term :=
| Var : nat -> term
| App : term -> term -> term 
| Lam : (*string ->*) term -> term.

Test term.
