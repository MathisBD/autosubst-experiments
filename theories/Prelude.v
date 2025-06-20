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

Record encoding (Shape : Type) (size : Shape -> nat) (A : Type) : Type :=
  { shape : Shape 
  ; elems : vec A (size shape) 
  }.
Arguments shape {Shape} {size} {A} e.
Arguments elems {Shape} {size} {A} e.

Class NormalFunctor (F : Type -> Type) :=
  (** Usual functor stuff. *)
  { map A B : (A -> B) -> F A -> F B
  ; map_id A (x : F A) : 
      map A A (fun a => a) x = x
  ; map_comp A B C (g : B -> C) (f : A -> B) (x : F A) :
      map B C g (map A B f x) = map A C (fun a => g (f a)) x
  (** Encoding as a vector. *)
  ; Shape : Type
  ; size : Shape -> nat
  ; encode {A} : F A -> encoding Shape size A
  ; decode {A} : encoding Shape size A -> F A
  ; encode_decode_inv {A} : forall x : F A, decode (encode x) = x
  }.
Arguments map F {NormalFunctor} {A} {B}.
Arguments Shape F {NormalFunctor}.
Arguments size F {NormalFunctor} {s}.
Arguments encode F {NormalFunctor} {A}.
Arguments decode F {NormalFunctor} {A}.

Module OptionNF.
  Definition Shape := bool.
  Definition size (b : bool) := if b then 1 else 0.

  Equations encode {A} (x : option A) : encoding Shape size A :=
  encode (Some a) := {| shape := true ; elems := [ a ] |} ;
  encode None := {| shape := false ; elems := [] |}.
    
  Equations decode {A} (x : encoding Shape size A) : option A :=
  decode {| shape := true ; elems := [ a ] |} := Some a ;
  decode {| shape := false ; elems := [] |} := None.
End OptionNF.

#[export, refine] 
Instance option_normal_functor : NormalFunctor option :=
  Build_NormalFunctor option option_map _ _ OptionNF.Shape OptionNF.size 
    (@OptionNF.encode) (@OptionNF.decode) _.
Proof.
- intros A [a|] ; cbn ; reflexivity.
- intros A B C g f [a|] ; cbn ; reflexivity.
- intros A [a|] ; cbn ; reflexivity.
Defined. 

Module ListNF.
  Definition Shape := nat.
  Definition size (n : nat) := n.

  Definition encode {A} (x : list A) : encoding Shape size A :=
    {| shape := List.length x ; elems := vec_of_list x |}.
    
  Definition decode {A} (x : encoding Shape size A) : list A :=
    list_of_vec (elems x).
End ListNF.

#[export, refine] 
Instance list_normal_functor : NormalFunctor list :=
  Build_NormalFunctor list List.map _ _ ListNF.Shape ListNF.size 
    (@ListNF.encode) (@ListNF.decode) _.
Proof.
- intros A x. now rewrite List.map_id.
- intros A B C g f x. now rewrite List.map_map.
- intros A x. induction x ; cbn; [reflexivity | now f_equal].
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
