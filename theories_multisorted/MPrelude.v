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
(*#[export] Hint Extern 5 => f_equal : core.
#[export] Hint Extern 5 => subst : core.*)

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
Definition eq1 {A B} : relation (A -> B) :=
  fun f g => forall x, f x = g x.

Notation "f =₁ g" := (eq1 f g) (at level 75).

#[export] Instance eq1_refl {A B} : Reflexive (@eq1 A B).
Proof. intros ? ?. reflexivity. Qed.

#[export] Instance eq1_sym {A B} : Symmetric (@eq1 A B).
Proof. intros ? ? H ?. now rewrite H. Qed.

#[export] Instance eq1_trans {A B} : Transitive (@eq1 A B).
Proof. intros ? ? ? H1 H2 ?. now rewrite H1, H2. Qed.

(* #[export] Instance eq1_equiv A B : Equivalence (@eq1 A B) :=
Proof.
constructor. ; [apply eq1_refl | |].
Build_Equivalence eq1 eq1_refl eq1_sym eq1_trans.*)

(** Pointwise equality on functions with two arguments. *)
Definition eq2 {A B C} : relation (A -> B -> C) :=
  fun f g => forall x, f x =₁ g x.

Notation "f =₂ g" := (eq2 f g) (at level 75).

#[export] Instance eq2_refl {A B C} : Reflexive (@eq2 A B C).
Proof. intros ? ? ?. reflexivity. Qed.

#[export] Instance eq2_sym {A B C} : Symmetric (@eq2 A B C).
Proof. intros ? ? H ? ?. now rewrite H. Qed.

#[export] Instance eq2_trans {A B C} : Transitive (@eq2 A B C).
Proof. intros ? ? ? H1 H2 ? ?. now rewrite H1, H2. Qed.

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
Definition up_ren (r : ren) : ren := 
  rcons 0 (rcomp r rshift).

#[export] Instance up_ren_proper : Proper (eq1 ==> eq1) up_ren.
Proof. intros ? ? H. unfold up_ren. now rewrite H. Qed.

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
  + right. intros H. apply n. now depelim H.
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

(** [vector_init n f] creates the vector of length [n] with elements 
    [f 0], [f 1], [f 2], etc. *)
Equations vector_init {T} (n : nat) (f : fin n -> T) : vector T n :=
vector_init 0 _ := vnil ;
vector_init (S n) f := vcons (f finO) (vector_init n (fun i => f (finS i))).

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
