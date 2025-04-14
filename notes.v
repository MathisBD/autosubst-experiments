
(* 1. Comparing level two terms/expressions.
   Switch from (x =σ y) to (forall e, eval e x = eval e y). *)


(* 2. "meta-variables" inside natural numbers.
e.g. proving lemma:

Lemma test (i : nat) (r r' : ren) : 
  (i . r) >> r' =₁ r' i . (r >> r').

i can't be reifed to nat.

i -> (Q_mvar 0, env = [i])
*)

(**

(shift k) i -> k + i 
*)

(** Quoted natural. *)
Inductive qnat :=
(** Zero. *)
| Q_zero : qnat
(** Successor of a quoted natural. *) 
| Q_succ : qnat -> qnat
(** Addition of quoted naturals. *)
| Q_plus : qnat -> qnat -> qnat 
(** Explicit renaming applied to a quoted natural. *)
| Q_rapply : ren -> qnat -> qnat 
(** Quoted natural meta-variable. *)
| Q_mvar : mvar -> qnat

(** Explicit renaming. *)
with ren :=
(** Explicit shift. *)
| R_shift : qnat -> ren
(** Renaming expansion. *)
| R_cons : qnat -> ren -> ren
(** Left to right composition of renamings. *)
| R_comp : ren -> ren -> ren 
(** Renaming meta-variable. *)
| R_mvar : mvar -> ren.


(* 3. How to specify completeness of simplification?
Following "Completeness and Decidability of de Bruijn Substitution Algebra in Coq":
define irreducible forms directly as an inductive type/inductive predicate.

Problem: with meta-variables in naturals, normal forms are not clear.
i. specify reducible forms
ii. irreducible := not reducible
*)

(*

Q_plus x Q_zero = x

(t u)[s] -> t[s] u[s]

*)

(** Reducible quoted natural. *)
Inductive qred : qnat -> Prop :=
(** Congruence. *)
| QR_succ x : qred x -> qred (Q_succ x)
| QR_plus x y : qred x \/ qred y -> qred (Q_plus x y)
| QR_ren r x : rred r \/ qred x -> qred (Q_rapply r x)

(** Addition should pull out [Q_succ] from both arguments,
    and b right associated. *)
| QR_plus_zero_l x : qred (Q_plus x Q_zero)
| QR_plus_zero_r x : qred (Q_plus Q_zero x)
| QR_plus_plus_l x y z : qred (Q_plus (Q_plus x y) z)
| QR_plus_succ_l x y : qred (Q_plus (Q_succ x) y)
| QR_plus_succ_r x y : qred (Q_plus x (Q_succ y))

(* Renamings should be fully applied to their argument.  *)
| QR_ren_comp r1 r2 i : qred (Q_rapply (R_comp r1 r2) i)
| QR_ren_shift k i : qred (Q_rapply (R_shift k) i)
| QR_rcons_zero i r : qred (Q_rapply (R_cons i r) Q_zero)
| QR_rcons_succ i r k : qred (Q_rapply (R_cons i r) (Q_succ k))

(** Reducible renaming. *)
with rred : ren -> Prop :=
(** Congruence. *)
| RR_shift k : qred k -> rred (R_shift k)
| RR_cons i r : qred i \/ rred r -> rred (R_cons i r)
| RR_comp r1 r2 : rred r1 \/ rred r2 -> rred (R_comp r1 r2)

(** Composition should be right associated. *)
| RR_rid_l r : rred (R_comp rid r)
| RR_rid_r r : rred (R_comp r rid)
| RR_comp_l r1 r2 r3 : rred (R_comp (R_comp r1 r2) r3)

(** Renaming simplification. *)
| RR_cons_l i r1 r2 : rred (R_comp (R_cons i r1) r2)
| RR_shift_l k r : 
  is_rshift r \/ is_rshift_l r -> rred (R_comp (R_shift k) r)
| RR_shift_cons k r : 
  is_rcons r -> rred (R_comp (R_shift (Q_succ k)) r).

Definition qirred x := ~ qred x.
Definition rirred r := ~ rred r.

(*

(forall e, eval e x = eval e y) -> simp x =R simp y

*)



(* 4. How to orient sigma-calculus equations? 

sid >> s = s
shift >> (t . s) = s

Push substitutions/renamings inside terms:
(t u)[s] = t[s] u[s]
(lambda. t)[s] = lambda. t[up_subst s]
(Var i)[r] = Var (r i)
(Var i)[s] = s i

t[s][s'] = t[s >> s']
r' (r i) = (r >> r') i

S_ren (i . r) >> s = s i . (S_ren r >> s)
s (r i) = (S_ren r >> s) i

t[(i . r) >> s] -> t<i . r>[s]
                -> t[s i . (r >> s)]

Curien paper -> other normal forms? with renamings?
PAM paper
sigma-sp calculus confluent + terminating


*)