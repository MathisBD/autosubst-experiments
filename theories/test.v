From Equations Require Import Equations.

Inductive fin : nat -> Type :=
| finO {n} : fin (S n)
| finS {n} : fin n -> fin (S n).

Definition cast {n m} (e : n = m) (f : fin n) : fin m :=
  match e with eq_refl => f end.

Lemma cast_K n (e : n = n) f :
  cast e f = f.
Proof.
  pose proof (Eqdep_dec.UIP_refl_nat _ e) as ->.
  reflexivity.
Qed.

Inductive sub : nat -> nat -> Type :=
| shift {n} m : sub n (m + n)
| comp {n m o} (s1 : sub n m) (s2 : sub m o) : sub n o.

Definition cast_sub {k n m} (e : n = m) (s : sub k n) : sub k m :=
  match e with eq_refl => s end.

Lemma cast_subs_K k n (e : n = n) (s : sub k _) :
  cast_sub e s = s.
Proof.
  pose proof (Eqdep_dec.UIP_refl_nat _ e) as ->.
  reflexivity.
Qed.

Equations tail {n m} (s : sub (S n) m) : sub n m :=
  tail (shift k) := cast_sub _ (shift (S k)) ;
  tail s := comp (shift 1) s.

Inductive normal : forall {n m}, sub n m -> Prop :=
| normal_shift {n m} : normal (shift (n:=n) m).

Lemma cast_normal n m m' s e :
  @normal n m s ->
  @normal n m' (cast_sub e s).
Proof.
  subst. rewrite cast_subs_K. auto.
Qed.

Lemma normal_tail n m s :
  normal (@tail n m s).
Proof.
funelim (tail s).
- clear.
  set (e := _ n k).
  clearbody e.
  set (x := k + S n) in *. clearbody x.
  subst. cbn.
  apply (@normal_shift n (S k)).
- admit. 
Admitted.

Reserved Notation "s1 '=σ' s2" (at level 75, no associativity).

Inductive seq : forall {n m}, sub n m -> sub n m -> Prop :=
| seq_shift_r n k : @shift n (S k) =σ comp (shift k) (shift 1)
where "s1 '=σ' s2" := (seq s1 s2).

Lemma seq_tail n m (s : sub (S n) m) :
  tail s =σ comp (shift 1) s.
Proof.
funelim (tail s).
- clear. Set Printing Implicit.
  set (e := _ n k). clearbody e.
  set (x := k + S n) in *.
  (* Le terme de droite dépend de la définition de [x] pour typechecker. *)
  Fail clearbody x.
  (* Si on efface le terme de droite ça marche: *)
  set (t := comp _ _) in *. clearbody t.
  clearbody x.
  (* Mais on peut plus prouver le résultat... *)