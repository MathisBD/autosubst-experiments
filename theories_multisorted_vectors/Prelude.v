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

#[export] Instance fin_EqDec n : EqDec (fin n).
Proof. intros i i'. destruct (eqb_fin_spec i i') ; constructor ; assumption. Defined.

(*Derive Signature for reflect.

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
Qed. *)

(*********************************************************************************)
(** *** Vectors. *)
(*********************************************************************************)

(** [vector T n] is the type of vectors of length [n] with elements in [T].
    It uses the standard encoding for fixed length vectors. *)
Inductive vector (T : Type) : nat -> Type :=
| vnil : vector T 0 
| vcons n : T -> vector T n -> vector T (S n).
Arguments vnil {T}.
Arguments vcons {T n}.

Derive Signature NoConfusion NoConfusionHom for vector.

(** Notation for vectors, in scope [vector]. *)

Declare Scope vector_scope.
Bind Scope vector_scope with vector.
Delimit Scope vector_scope with vector.

Notation "[-  -]" := vnil : vector_scope. 
Notation "[-  x  -]" := (vcons x vnil) : vector_scope.
Notation "[-  x ; y ; .. ; z  -]" := (vcons x (vcons y .. (vcons z vnil) ..)) : vector_scope.

(*********************************************************************************)
(** *** Operations on vectors. *)
(*********************************************************************************)

(** [vector_init n f] creates the vector of length [n] with elements 
    [f 0], [f 1], [f 2], etc. *)
Equations vector_init {T} (n : nat) (f : fin n -> T) : vector T n :=
vector_init 0 _ := vnil ;
vector_init (S n) f := vcons (f finO) (vector_init n (fun i => f (finS i))).

(** [vector_nth xs i] looks up the [i]-th element of [xs]. Contrary to lists,
    this does not return an [option T] or require a default element in [T]. *)
Equations vector_nth {T n} (xs : vector T n) (i : fin n) : T :=
vector_nth (vcons x xs) finO     := x ;
vector_nth (vcons x xs) (finS i) := vector_nth xs i.

(** [vector_map f xs] maps function [f] over vector [xs]. *)
Equations vector_map {T U n} (f : T -> U) (xs : vector T n) : vector U n :=
vector_map f vnil := vnil ;
vector_map f (vcons x xs) := vcons (f x) (vector_map f xs). 

(** [vector_mapi f xs] maps function [f] over vector [xs].
    [f] has access to the index of the element as a [fin n].  *)
Equations vector_mapi {T U n} (f : fin n -> T -> U) (xs : vector T n) : vector U n :=
vector_mapi f vnil := vnil ;
vector_mapi f (vcons x xs) := vcons (f finO x) (vector_mapi (fun i => f (finS i)) xs). 

(** [vector_map2 f xs ys] maps the binary function [f] over vectors [xs] and [ys]. *)
Equations vector_map2 {T1 T2 U n} (f : T1 -> T2 -> U) (xs : vector T1 n) (ys : vector T2 n) : vector U n :=
vector_map2 f vnil vnil := vnil ;
vector_map2 f (vcons x xs) (vcons y ys) := vcons (f x y) (vector_map2 f xs ys). 

(*********************************************************************************)
(** *** Setoid rewrite on vectors. *)
(*********************************************************************************)

Section VectorEq.
  Context {T : Type} (R : relation T) (H : Equivalence R).

  (** Two vectors are equal according to [vector_eq R] if their elements are 
      equal according to [R]. *)
  Definition vector_eq {n} : relation (vector T n) :=
    fun xs ys =>
      forall i : fin n, R (vector_nth xs i) (vector_nth ys i). 

  #[export] Instance vector_eq_equiv n : Equivalence (@vector_eq n).
  Proof. 
  constructor.
  - intros xs i. reflexivity.
  - intros xs ys Hsym i. now symmetry.
  - intros xs ys zs H1 H2 i. etransitivity ; eauto.
  Qed. 

  Lemma vector_eq_vcons_inv {n} (x x' : T) (xs xs' : vector T n) :
    vector_eq (vcons x xs) (vcons x' xs') ->
    R x x' /\ vector_eq xs xs'.
  Proof. 
  intros H'. split.
  - specialize (H' finO). exact H'.
  - intros i. specialize (H' (finS i)). exact H'.
  Qed.

End VectorEq. 

#[export] Instance vector_map_proper {T U n} (RT : relation T) (RU : relation U) : 
  Proper ((RT ==> RU) ==> vector_eq RT ==> vector_eq RU) (@vector_map T U n). 
Proof.
intros f f' Hf xs xs' Hxs i. 
induction i ; depelim xs ; depelim xs' ; simp vector_nth vector_map.
- apply Hf. now apply vector_eq_vcons_inv in Hxs.
- apply IHi. now apply vector_eq_vcons_inv in Hxs.
Qed.

#[export] Instance vector_mapi_proper {T U n} (RT : relation T) (RU : relation U) : 
  Proper ((eq ==> RT ==> RU) ==> vector_eq RT ==> vector_eq RU) (@vector_mapi T U n). 
Proof.
intros f f' Hf xs xs' Hxs i.
induction i ; depelim xs ; depelim xs' ; simp vector_nth vector_mapi.
- apply Hf ; try reflexivity. now apply vector_eq_vcons_inv in Hxs.
- apply IHi.
  + clear -Hf. intros i ? <- x x' Hx. now apply Hf. 
  + now apply vector_eq_vcons_inv in Hxs.
Qed.

#[export] Instance vector_map2_proper {T1 T2 U n} 
  (RT1 : relation T1) (RT2 : relation T2) (RU : relation U) : 
  Proper ((RT1 ==> RT2 ==> RU) ==> vector_eq RT1 ==> vector_eq RT2 ==> vector_eq RU) 
    (@vector_map2 T1 T2 U n). 
Proof. 
intros f f' Hf xs xs' Hxs ys ys' Hys i.
induction i ; depelim xs ; depelim xs' ; depelim ys ; depelim ys' ; simp vector_nth vector_map2.
- apply Hf ; try reflexivity. 
  + now apply vector_eq_vcons_inv in Hxs.
  + now apply vector_eq_vcons_inv in Hys.
- apply IHi.
  + now apply vector_eq_vcons_inv in Hxs.
  + now apply vector_eq_vcons_inv in Hys.
Qed.

(*********************************************************************************)
(** *** Heterogeneous vectors. *)
(*********************************************************************************)

(** [hvector n T] is the type of vectors of length [n] with the [i]-th element
    of type [T i]. Note that we use a function [fin n -> Type] to give the types
    of the elements, instead of the standard encoding using a type [A], a vector 
    [vector n A] and a function [A -> Type]. *)
Polymorphic Inductive hvector : forall n, (fin n -> Type) -> Type :=
| hnil {T} : hvector 0 T
| hcons {n T} : T finO -> hvector n (fun i => T (finS i)) -> hvector (S n) T.

Derive Signature NoConfusion NoConfusionHom for hvector.

(** Notations for heterogeneous vectors, in scope [hvector]. *)

Declare Scope hvector_scope.
Bind Scope hvector_scope with hvector.
Delimit Scope hvector_scope with hvector.

Notation "[=  =]" := hnil : hvector_scope.
Notation "[=  x  =]" := (hcons x hnil) : hvector_scope.
Notation "[=  x ; y ; .. ; z  =]" := (hcons x (hcons y .. (hcons z hnil) ..)) : hvector_scope.

(*********************************************************************************)
(** *** Operations on heterogeneous vectors. *)
(*********************************************************************************)

(** Convert a homogeneous vector into a heterogeneous vector. *)
Equations hvector_of_vector {n T} (xs : vector T n) : hvector n (fun _ => T) :=
hvector_of_vector vnil := hnil ;
hvector_of_vector (vcons x xs) := hcons x (hvector_of_vector xs).

(** [hvector_init n f] creates the heterogeneous vector of length [n] with elements 
    [f 0], [f 1], [f 2], etc. *)
Equations hvector_init (n : nat) {T : fin n -> Type} (f : forall i, T i) : hvector n T :=
hvector_init 0 _ := hnil ;
hvector_init (S n) f := hcons (f finO) (hvector_init n (fun i => f (finS i))).

(** [hvector_nth xs i] looks up the [i]-th element of [xs], which has type [T i]. *)
Equations hvector_nth {n T} (h : hvector n T) (i : fin n) : T i :=
hvector_nth (hcons x xs) finO     := x ;
hvector_nth (hcons x xs) (finS i) := hvector_nth xs i.

(** [hvector_mapi f xs] maps function [f] over vector [xs]. 
    [f] has access to the index of the element as a [fin n]. *)
Equations hvector_mapi {n T U} (f : forall i, T i -> U i) (xs : hvector n T) : hvector n U :=
hvector_mapi f hnil := hnil ;
hvector_mapi f (hcons x xs) := hcons (f finO x) (hvector_mapi (fun i => f (finS i)) xs).

(** [hvector_mapi2 f xs ys] maps the binary function [f] over heterogeneous vectors [xs] and [ys]. *)
Equations hvector_mapi2 {n T1 T2 U} (f : forall i, T1 i -> T2 i -> U i) 
  (xs : hvector n T1) (ys : hvector n T2) : hvector n U :=
hvector_mapi2 f hnil hnil := hnil ;
hvector_mapi2 f (hcons x xs) (hcons y ys) := 
  hcons (f finO x y) (hvector_mapi2 (fun i => f (finS i)) xs ys). 

(*********************************************************************************)
(** *** Lemmas about heterogeneous vectors. *)
(*********************************************************************************)

Lemma hvector_nth_vector {n T} (xs : vector T n) i :
  hvector_nth (hvector_of_vector xs) i = vector_nth xs i.
Proof.
funelim (hvector_of_vector xs).
- depelim i.
- depelim i ; simp vector_nth hvector_nth. reflexivity.
Qed.

(*********************************************************************************)
(** *** Setoid rewrite on heterogeneous vectors. *)
(*********************************************************************************)

(** Equality on heterogeneous vectors. *)
Section HvectorEq.
  Context {n : nat} {T : fin n -> Type} (eq : forall i, relation (T i)) 
    (H : forall i, Equivalence (eq i)).

  (** Two heterogeneous vectors are equal according to [hvector_eq R] if their 
      elements are equal according to [R]. *)
  Definition hvector_eq : relation (hvector n T) :=
    fun xs ys =>
      forall i : fin n, eq i (hvector_nth xs i) (hvector_nth ys i). 

  #[export] Instance hvector_eq_equiv : Equivalence hvector_eq.
  Proof. 
  constructor.
  - intros xs i. reflexivity.
  - intros xs ys Hsym i. now symmetry.
  - intros xs ys zs H1 H2 i. etransitivity ; eauto.
  Qed. 

End HvectorEq.
  
(*Lemma hvector_eq_hcons_inv {n} {T : fin (S n) -> Type} (R : forall i, relation (T i)) 
  (x x' : T (@finO n)) (xs xs' : hvector (S n) T) :
  hvector_eq R (hcons x xs) (hcons x' xs') ->
  R x x' /\ hvector_eq R xs xs'.
Proof. 
intros H'. split.
- specialize (H' finO). exact H'.
- intros i. specialize (H' (finS i)). exact H'.
Qed.*)

#[export] Instance hvector_of_vector_proper {n T} (R : relation T) : 
  Proper (vector_eq R ==> hvector_eq (fun _ => R)) (@hvector_of_vector n T).
Proof. intros xs xs' H i. rewrite !hvector_nth_vector. apply H. Qed.

#[export] Instance hvector_mapi_proper {n} {T U : fin n -> Type} 
  (RT : forall i, relation (T i)) (RU : forall i, relation (U i)) : 
  let R : relation (forall i, T i -> U i) :=
    fun f f' =>
      forall i,
      forall (x x' : T i), RT i x x' ->
      RU i (f i x) (f' i x') 
  in
  Proper (R ==> hvector_eq RT ==> hvector_eq RU) 
    (@hvector_mapi n T U). 
Proof. Admitted.

#[export] Instance hvector_mapi2_proper {n} {T1 T2 U : fin n -> Type} 
  (RT1 : forall i, relation (T1 i)) (RT2 : forall i, relation (T2 i)) (RU : forall i, relation (U i)) : 
  let Rf : relation (forall i, T1 i -> T2 i -> U i) :=
    fun f f' =>
      forall i,
      forall (x x' : T1 i), RT1 i x x' ->
      forall (y y' : T2 i), RT2 i y y' ->
      RU i (f i x y) (f' i x' y') 
  in
  Proper (Rf ==> hvector_eq RT1 ==> hvector_eq RT2 ==> hvector_eq RU) 
    (@hvector_mapi2 n T1 T2 U). 
Proof. Admitted.

