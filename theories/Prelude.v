From Coq Require Export Bool Nat List String Morphisms Relations Program.Equality Lia.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
Export ListNotations.

#[export] Set Equations Transparent.

(** Just to make sure. *)
#[export] Unset Equations With UIP.

(** Ltac2 is still missing many basic Ltac1 tactics,
    so we use Ltac1 for proofs. *)
#[export] Set Default Proof Mode "Classic".

(** Coercion to view booleans as propositions. *)
Coercion is_true : bool >-> Sortclass.

(*********************************************************************************)
(** *** Convenience tactics. *)
(*********************************************************************************)

(** Add some power to [auto] and variants (such as [triv]). *)
#[export] Hint Extern 5 => f_equal : core.
#[export] Hint Extern 5 => subst : core.

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

(** Surprisingly, neither [eauto] nor [easy] is more powerful than the other. *)
Ltac triv := try solve [ eauto | easy ].

(** Unfold all local definitions from the proof context,
    then clear the definitions. *)
Ltac unfold_all :=
  repeat match goal with 
  | [ x := _ |- _ ] => unfold x in * ; clear x
  end.

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
Equations rcons (i0 : nat) (r : ren) : ren :=
rcons i0 _ 0 := i0 ;
rcons i0 r (S i) := r i.

(** Compose two renamings (left to right composition). *)
Equations rcomp (r1 r2 : ren) : ren :=
rcomp r1 r2 i := r2 (r1 i).

(** Lift a renaming through a binder. *)
Equations up_ren (r : ren) : ren := 
up_ren r := rcons 0 (rcomp r rshift).

(*********************************************************************************)
(** *** Trivial properties of renamings. *)
(*********************************************************************************)

(** Pointwise equality for functions. *)
Definition point_eq {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (point_eq f g) (at level 75).

Lemma peq_refl {A B} {x : A -> B} : x =₁ x.
Proof. reflexivity. Qed.

Lemma peq_sym {A B} {x y : A -> B} : x =₁ y -> y =₁ x.
Proof. now intros ->. Qed.

Lemma peq_trans {A B} {x y z : A -> B} : x =₁ y -> y =₁ z -> x =₁ z.
Proof. now intros -> ->. Qed.

Lemma congr_rcons i {r r'} :
  r =₁ r' -> rcons i r =₁ rcons i r'.
Proof. intros H [|i'] ; [reflexivity|]. now simp rcons. Qed.

Lemma congr_rcomp {r1 r1' r2 r2'} :
  r1 =₁ r1' -> r2 =₁ r2' -> rcomp r1 r2 =₁ rcomp r1' r2'.
Proof. intros H1 H2 i. simp rcomp. now rewrite H1, H2. Qed.

Lemma congr_up_ren {r r'} :
  r =₁ r' -> up_ren r =₁ up_ren r'.
Proof. intros H. simp up_ren. apply congr_rcons. now apply congr_rcomp. Qed.

(*********************************************************************************)
(** *** Finite sets. *)
(*********************************************************************************)

(** [fin n] represents the finite set with [n] elements [0], [1], ..., [n-1]. *)
Inductive fin : nat -> Type :=
| (** [0] is in [fin n] whenever [n > 0]. *)
  finO {n} : fin (S n)
| (** Injection from [fin n] to [fin (S n)], which maps [i] to [i+1]. *)
  finS {n} : fin n -> fin (S n).

Derive Signature NoConfusion NoConfusionHom for fin.

(** Boolean equality test on [fin n]. We do an ugly convoy pattern by hand
    instead of using Equations because we want [eqb_fin] to unfold nicely 
    with [cbv]. *)
Fixpoint eqb_fin {n} (i i' : fin n) : bool :=
  match i in fin n0 return fin n0 -> bool with 
  | finO => fun i' => match i' with finO => true | finS _ => false end
  | finS i => fun i' => 
    match i' in fin (S n1) return fin n1 -> bool with 
    | finO => fun _ => false 
    | finS i' => fun i => eqb_fin i i' 
    end i
  end i'.

Lemma eqb_fin_spec {n} (i i' : fin n) : reflect (i = i') (eqb_fin i i').
Proof.
induction i ; depelim i'.
- now left.
- right. intros H. depelim H.
- right. intros H. depelim H.
- simpl. destruct (IHi i') ; subst.
  + now left.
  + right. intros H. now depelim H.
Qed.  

#[export] Instance fin_EqDec n : EqDec (fin n).
Proof. intros i i'. destruct (eqb_fin_spec i i') ; triv. Qed.

(*********************************************************************************)
(** *** Fixed length vectors. *)
(*********************************************************************************)

(** [vector T n] is the type of vectors of length [n] with elements in [T]. *)
Inductive vector (T : Type) : nat -> Type :=
| vnil : vector T 0 
| vcons n : T -> vector T n -> vector T (S n).
Arguments vnil {T}.
Arguments vcons {T n}.

Derive Signature NoConfusion NoConfusionHom for vector.

(** [vector_nth i xs] looks up the [i]-th element of [xs]. Contrary to lists,
    this does not return an [option T] or require a default element in [T]. 
    We do a convoy pattern by hand for the same reason as in [eqb_fin]. *)
Fixpoint vector_nth {T n} (i : fin n) (xs : vector T n) : T :=
  match i in fin n0 
  return vector T n0 -> T 
  with 
  | finO => fun xs => 
    match xs in vector _ n1
    return match n1 with 0 => unit | S _ => T end
    with
    | vnil => tt 
    | vcons x xs => x 
    end
  | finS i => fun xs =>
    match xs in vector _ n1 
    return match n1 with 0 => unit -> unit | S n1 => fin n1 -> T end
    with 
    | vnil => fun _ => tt
    | vcons x xs => fun i => vector_nth i xs 
    end i
  end xs.  
