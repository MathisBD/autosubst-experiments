From Coq Require Export Bool Nat List String Morphisms Relations Program.Equality Lia.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
From Utils Require Export Fin Vector.
Export ListNotations VectorNotations.

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
Definition eq1 {A B} : relation (A -> B) := pointwise_relation _ eq.
Notation "f =₁ g" := (eq1 f g) (at level 75).

Lemma eq1_refl {A B} {x : A -> B} : x =₁ x.
Proof. reflexivity. Qed.

Lemma eq1_sym {A B} {x y : A -> B} : x =₁ y -> y =₁ x.
Proof. now intros ->. Qed.

Lemma eq1_trans {A B} {x y z : A -> B} : x =₁ y -> y =₁ z -> x =₁ z.
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
(** *** Normal functors. *)
(*********************************************************************************)

Class NormalFunctor (F : Type -> Type) :=
  (** Usual functor stuff. *)
  { map {A B} : (A -> B) -> F A -> F B
  ; map_id A (f : A -> A) (x : F A) : 
      f =₁ id -> 
      map f x = x
  ; map_comp A B C (f : A -> C) (f1 : A -> B) (f2 : B -> C) (x : F A) :
      (fun a => f2 (f1 a)) =₁ f -> 
      map f2 (map f1 x) = map f x
  (** Encoding as a vector. *)
  ; shape : Type
  ; size : shape -> nat
  ; encode_shape {A} : F A -> shape
  ; encode_elems {A} : forall (x : F A), vec A (size (encode_shape x))
  ; decode {A} : forall sh, vec A (size sh) -> F A
  ; encode_decode_map {A B} (f : A -> B) (x0 : F A) : 
      let x1 := encode_elems x0 in 
      let x2 := vec_map f x1 in 
      let x3 := decode (encode_shape x0) x2 in 
      x3 = map f x0
  }.
Arguments map F {NormalFunctor} {A} {B}.
Arguments shape F {NormalFunctor}.
Arguments size F {NormalFunctor} {s}.
Arguments encode_shape F {NormalFunctor} {A}.
Arguments encode_elems F {NormalFunctor} {A}.
Arguments decode F {NormalFunctor} {A}.

Module OptionNF.
  Definition shape := bool.
  Definition size (b : bool) := if b then 1 else 0.

  Equations encode_shape {A} (x : option A) : shape :=
  encode_shape (Some _) := true ;
  encode_shape None := false.

  Equations encode_elems {A} (x : option A) : vec A (size (encode_shape x)) :=
  encode_elems (Some a) := [ a ] ;
  encode_elems None := [].
    
  Equations decode {A} (sh : shape) (x : vec A (size sh)) : option A :=
  decode true  [ a ] := Some a ;
  decode false []    := None.
End OptionNF.

#[export, refine] 
Instance option_normal_functor : NormalFunctor option :=
  Build_NormalFunctor option option_map _ _ OptionNF.shape OptionNF.size 
    (@OptionNF.encode_shape) (@OptionNF.encode_elems) (@OptionNF.decode) _.
Proof.
- intros A f [a|] H ; cbn ; rewrite ?H ; reflexivity.
- intros A B C f f1 f2 [a|] H ; cbn ; rewrite ?H ; reflexivity.
- intros A B f [a|] ; cbn ; reflexivity.
Defined. 

Module ListNF.
  Definition shape := nat.
  Definition size (n : nat) := n.

  Definition encode_shape {A} (xs : list A) : shape :=
    List.length xs.

  Fixpoint encode_elems {A} (xs : list A) : vec A (size (encode_shape xs)) :=
    match xs with 
    | [] => vnil
    | x :: xs => vcons x (encode_elems xs)
    end. 
    
  Definition decode {A} (sh : shape) (elems : vec A (size sh)) : list A :=
    list_of_vec elems.
End ListNF.

#[export, refine] 
Instance list_normal_functor : NormalFunctor list :=
  Build_NormalFunctor list List.map _ _ ListNF.shape ListNF.size 
    (@ListNF.encode_shape) (@ListNF.encode_elems) (@ListNF.decode) _.
Proof.
- intros A f x H. induction x ; cbn ; [reflexivity | now rewrite H, IHx].
- intros A B C f f1 f2 x H. induction x ; cbn ; [reflexivity | now rewrite H, IHx].
- intros A B f x. induction x ; cbn ; [reflexivity | now f_equal].
Defined.

(*Equations vec_of_fin {n A} (f : fin n -> A) : vec A n :=
@vec_of_fin 0 _ _ := vnil ;
@vec_of_fin (S n) _ f := vcons (f finO) (vec_of_fin (fun i => f (finS i))).

Lemma vec_nth_of_fin {n A} (f : fin n -> A) i : 
  vec_nth (vec_of_fin f) i = f i.
Proof.
funelim (vec_of_fin f) ; depelim i ; simp vec_nth. reflexivity.
Qed.

Module PiNF.
Section WithN.
  Context (n : nat).

  Definition Shape := unit.
  Definition size (_ : unit) : nat := n.

  Definition encode {A} (x : fin n -> A) : encoding (fun A => fin n -> A) Shape size A :=
    {| shape := tt ; elems := vec_of_fin x |}.
    
  Definition decode {A} (x : encoding (fun A => fin n -> A) Shape size A) : fin n -> A :=
    vec_nth (elems x).
    
  Lemma encode_decode_inv A (x : fin n -> A) : decode (encode x) = x.
  Proof. unfold encode, decode. cbn. Fail apply vec_nth_of_fin. Qed.
End PiNF.
*)
