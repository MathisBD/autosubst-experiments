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

(** Coercion from [fin n] to [nat]. *)
Equations fin_to_nat {n} : fin n -> nat :=
fin_to_nat finO := 0 ;
fin_to_nat (finS i) := S (fin_to_nat i).

(** Boolean equality test on [fin n]. *)
Equations eqb_fin {n} : fin n -> fin n -> bool :=
eqb_fin finO finO := true ;
eqb_fin (finS i) (finS i') := eqb_fin i i' ;
eqb_fin _ _ := false.

Lemma eqb_fin_spec {n} (i i' : fin n) : reflect (i = i') (eqb_fin i i').
Proof.
funelim (eqb_fin i i').
- now left.
- right. intros H. depelim H.
- right. intros H. depelim H.
- destruct H ; subst.
  + now left.
  + right. intros H. apply n. depelim H. triv.
Qed.     

Derive Signature for reflect.

Equations fin_existsb (n : nat) (P : fin n -> bool) : bool :=
fin_existsb 0 _ := false ;
fin_existsb (S n) P := P finO || fin_existsb n (fun i => P (finS i)).

Lemma fin_existsb_spec (n : nat) (P : fin n -> bool) :
  reflect (exists i, P i) (fin_existsb n P).
Proof.
funelim (fin_existsb n P).
- right. intros (? & H). depelim x.
- destruct (P finO) eqn:E ; simpl.
  + left. exists finO. now rewrite E.
  + destruct (fin_existsb n (fun i => P (finS i))).
    * left. depelim H. destruct e as (i & H). eauto.
    * right. intros (i & H'). depelim H. apply n0. depelim i.
      --now rewrite E in H'.
      --eauto.
Qed. 

(*********************************************************************************)
(** *** Fixed length vectors. *)
(*********************************************************************************)

(** [vector T n] is the type of vectors of length [n] with elements in [T].
    It uses the standard encoding for fixed length vectors. *)
Inductive vector (T : Type) : nat -> Type :=
| vnil : vector T 0 
| vcons n : T -> vector T n -> vector T (S n).
Arguments vnil {T}.
Arguments vcons {T n}.

Derive Signature NoConfusion NoConfusionHom for vector.

(** [vector_nth i xs] looks up the [i]-th element of [xs]. Contrary to lists,
    this does not return an [option T] or require a default element in [T]. *)
Equations vector_nth {T n} (i : fin n) (xs : vector T n) : T :=
vector_nth finO (vcons x xs) := x ;
vector_nth (finS i) (vcons x xs) := vector_nth i xs.

(** [vector_map f xs] maps function [f] over vector [xs]. *)
Equations vector_map {T U n} (f : T -> U) (xs : vector T n) : vector U n :=
vector_map f vnil := vnil ;
vector_map f (vcons x xs) := vcons (f x) (vector_map f xs). 

(** [vector_map_nth f i xs] maps [f] on the [i]-th element of [xs],
    and leaves other elements untouched. *)
Equations vector_map_nth {T n} (f : T -> T) (i : fin n) (xs : vector T n) : vector T n := 
vector_map_nth f finO (vcons x xs) := vcons (f x) xs ;
vector_map_nth f (finS i) (vcons x xs) := vcons x (vector_map_nth f i xs).

(** Notation for vectors, in scope [vector]. *)

Declare Scope vector_scope.
Bind Scope vector_scope with vector.
Delimit Scope vector_scope with vector.

Notation "[-  -]" := vnil : vector_scope. 
Notation "[-  x  -]" := (vcons x vnil) : vector_scope.
Notation "[-  x ; y ; .. ; z  -]" := (vcons x (vcons y .. (vcons z vnil) ..)) : vector_scope.

(*********************************************************************************)
(** *** Fixed length _heterogeneous_ vectors. *)
(*********************************************************************************)

(** [hvector n T] is the type of vectors of length [n] with the [i]-th element
    of type [T i]. Note that we use a function [fin n -> Type] to give the types
    of the elements, instead of the standard encoding using a type [A], a vector 
    [vector n A] and a function [A -> Type]. *)
Polymorphic Inductive hvector : forall n, (fin n -> Type) -> Type :=
| hnil {T} : hvector 0 T
| hcons {n T} : T finO -> hvector n (fun i => T (finS i)) -> hvector (S n) T.

Derive Signature NoConfusion NoConfusionHom for hvector.

(** [hvector_nth i xs] looks up the [i]-th element of [xs], which has type [T i]. *)
Polymorphic Equations hvector_nth {n T} (i : fin n) (h : hvector n T) : T i :=
hvector_nth finO (hcons x xs) := x ;
hvector_nth (finS i) (hcons x xs) := hvector_nth i xs.

(** [hvector_map f xs] maps function [f] over vector [xs]. 
    [f] has access to the index of the element as a [fin n]. *)
Polymorphic Equations hvector_map {n T U} (f : forall i, T i -> U i) (xs : hvector n T) : hvector n U :=
hvector_map f hnil := hnil ;
hvector_map f (hcons x xs) := hcons (f finO x) (hvector_map (fun i => f (finS i)) xs).

(** Notations for heterogeneous vectors, in scope [hvector]. *)

Declare Scope hvector_scope.
Bind Scope hvector_scope with hvector.
Delimit Scope hvector_scope with hvector.

Notation "[=  =]" := hnil : hvector_scope.
Notation "[=  x  =]" := (hcons x hnil) : hvector_scope.
Notation "[=  x ; y ; .. ; z  =]" := (hcons x (hcons y .. (hcons z hnil) ..)) : hvector_scope.
