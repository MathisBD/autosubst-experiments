From Coq Require Export Nat List String Morphisms Relations Program.Equality Lia.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
Export ListNotations.

(** Ltac2 is still missing many basic Ltac1 tactics,
    so I use Ltac1 for proofs. *)
#[export] Set Default Proof Mode "Classic".

Coercion is_true : bool >-> Sortclass.

(** Convenience tactics. *)

(** Simplify equations of the form [existT ?a ?b _ = existT ?a ?b _], 
    which are often generates by Rocq's [inversion] tactic. *)
Ltac simpl_existT :=
  match goal with 
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H 
  | _ => idtac
  end.

(** Run [inversion H], and cleanup the resulting equations. *)
Ltac inv H := 
  inversion H ; repeat first [ progress subst | progress simpl_existT ].

(** Split n-ary conjunctions. *)
Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].

(** On a hypothesis of the form [H : A -> B], this generates two goals:
    - the first asks to prove [A]. 
    - the second asks to prove the original goal, 
      in a context where [H : B]. *)
Ltac feed H := 
  match type of H with 
  | ?A -> ?B => 
    let HA := fresh "H" in 
    assert (HA : A) ; [| specialize (H HA)]
  end.

Ltac feed2 H := feed H ; [| feed H].
Ltac feed3 H := feed H ; [| feed2 H].
Ltac feed4 H := feed H ; [| feed3 H].

(** Surprisingly, neither [eauto] nor [easy] is more powerful than the other. *)
Ltac triv := try solve [ eauto | easy ].

(** Unfold all local definitions from the proof context,
    then clear the definitions. *)
Ltac unfold_all :=
  repeat match goal with 
  | [ x := _ |- _ ] => unfold x in * ; clear x
  end.

(** Pointwise equality for functions. *)
Definition point_eq {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (point_eq f g) (at level 75).

(** A renaming on terms is a function [nat -> nat] which is applied
    to all free variables. *)
Definition ren := nat -> nat.

(** The identity renaming. *)
Definition rid : ren := fun i => i.

(** [rshift] shifts indices by one. *)
Definition rshift : ren := fun i => S i.

(** Cons an index with a renaming. *)
Equations rcons (i0 : nat) (r : ren) : ren :=
rcons i0 _ 0 := i0 ;
rcons i0 r (S i) := r i.

(** Compose two renamings (left to right composition). *)
Equations rcomp (r1 r2 : ren) : ren :=
rcomp r1 r2 i := r2 (r1 i).

(** Lift a renaming through a binder. *)
Equations up_ren (r : ren) : ren := 
up_ren r := rcons 0 (rcomp r rshift).

(*(** [fin n] represents the finite set with [n] elements [0], [1], ..., [n-1]. *)
Inductive fin : nat -> Type :=
| (** [0] is in [fin n] whenever [n > 0]. *)
  fin_zero {n} : fin (S n)
| (** Injection from [fin n] to [fin (S n)], which maps [i] to [i+1]. *)
  fin_succ {n} : fin n -> fin (S n).

(** Mapping from [i] to [i + k]. *)
Equations fin_weaken {n} (k : nat) (i : fin n) : fin (k + n) :=
fin_weaken 0 i := i ;
fin_weaken (S k) i := fin_succ (fin_weaken k i).*)
