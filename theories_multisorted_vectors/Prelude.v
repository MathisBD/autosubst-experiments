From Coq Require Export Bool Nat List String Morphisms Relations Program.Equality Lia.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
From Utils Require Export Fin Vector Hvector.
Export ListNotations.

(** Enable reducing constants defined using [Equations]. *)
#[export] Set Equations Transparent.

(** Just to make sure. *)
#[export] Unset Equations With UIP.

(** Ltac2 is still missing many basic tactics and notations, so we use Ltac1 for proofs. *)
#[export] Set Default Proof Mode "Classic".

(** Coercion to view booleans as propositions in [Prop]. *)
Coercion is_true : bool >-> Sortclass.

(*********************************************************************************)
(** *** Convenience tactics. *)
(*********************************************************************************)

(** Split n-ary conjunctions. *)
Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].

(** On a hypothesis of the form [H : A -> B], this generates two goals:
    - the first asks to prove [A]. 
    - the second asks to prove the original goal in a context where [H : A]. *)
Ltac feed H := 
  match type of H with 
  | ?A -> ?B => 
    let HA := fresh "H" in 
    assert (HA : A) ; [| specialize (H HA)]
  end.

Ltac feed2 H := feed H ; [| feed H].
Ltac feed3 H := feed H ; [| feed2 H].
Ltac feed4 H := feed H ; [| feed3 H].

(*********************************************************************************)
(** *** Pointwise equality on functions. *)
(*********************************************************************************)

(** Pointwise equality on functions with one argument. *)
Definition eq1 {A B} : relation (forall a : A, B a) :=
  fun f g => forall x, f x = g x.

Notation "f =₁ g" := (eq1 f g) (at level 75).

#[export] Instance eq1_refl {A B} : Reflexive (@eq1 A B).
Proof. intros ? ?. reflexivity. Qed.

#[export] Instance eq1_sym {A B} : Symmetric (@eq1 A B).
Proof. intros ? ? H ?. now rewrite H. Qed.

#[export] Instance eq1_trans {A B} : Transitive (@eq1 A B).
Proof. intros ? ? ? H1 H2 ?. now rewrite H1, H2. Qed.

#[export] Instance eq1_equiv A B : Equivalence (@eq1 A B).
Proof. constructor ; typeclasses eauto. Qed.

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** A renaming on terms is a function [nat -> nat] which is applied
    to all free variables. *)
Definition ren := nat -> nat.

(** The identity renaming. *)
Definition rid : ren := fun i => i.

(** [rshift] shifts indices by one. *)
Definition rshift : ren := fun i => S i.

(** Cons an index with a renaming. *)
Definition rcons (i0 : nat) (r : ren) : ren :=
  fun i =>
    match i with 
    | 0 => i0 
    | S i => r i 
    end. 

#[export] Instance rcons_proper : Proper (eq ==> eq1 ==> eq1) rcons.
Proof. intros i0 ? <- r r' Hr [|i] ; [reflexivity|]. cbn. apply Hr. Qed.
  
(** Compose two renamings (left to right composition). *)
Definition rcomp (r1 r2 : ren) : ren :=
  fun i => r2 (r1 i).

#[export] Instance rcomp_proper : Proper (eq1 ==> eq1 ==> eq1) rcomp.
Proof. intros ? ? H1 ? ? H2 i. cbv. now rewrite H1, H2. Qed.

(** Lift a renaming through a binder. *)
Definition rup (r : ren) : ren := 
  rcons 0 (rcomp r rshift).

#[export] Instance rup_proper : Proper (eq1 ==> eq1) rup.
Proof. intros ? ? H. unfold rup. now rewrite H. Qed.


