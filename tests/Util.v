From Coq Require Import Utf8 List Bool.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".

Notation "'∑' x .. y , p" := (sigT (λ x, .. (sigT (λ y, p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Ltac forall_iff_impl T :=
  lazymatch eval cbn beta in T with
  | forall x : ?A, @?T' x =>
    let y := fresh x in
    refine (forall y, _) ;
    forall_iff_impl (@T' x)
  | ?P ↔ ?Q => exact (P → Q)
  | _ => fail "not a quantified ↔"
  end.

Ltac wlog_iff_using tac :=
  lazymatch goal with
  | |- ?G =>
    let G' := fresh in
    unshelve refine (let G' : Prop := _ in _) ; [ forall_iff_impl G |] ;
    let h := fresh in
    assert (h : G') ; [
      subst G'
    | subst G' ; intros ; split ; eauto ; apply h ; clear h ; tac
    ]
  end.

Ltac wlog_iff :=
  wlog_iff_using firstorder.

Create HintDb shelvedb.

Hint Extern 10000 => shelve : shelvedb.

Ltac destruct_if e :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn: e
  end.

Ltac destruct_if' :=
  let e := fresh "e" in
  destruct_if e.

Ltac destruct_ifs :=
  repeat destruct_if'.

Ltac destruct_bool b :=
  lazymatch b with
  | negb ?b => destruct_bool b
  | ?b && ?c => destruct_bool b
  | _ => let e := fresh "e" in destruct b eqn: e
  end.

Ltac d_if :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct_bool b
  end.

Section Inb.

  Context {A} (eqb : A → A → bool).

  Definition inb (a : A) (l : list A) :=
    existsb (eqb a) l.

  Definition inclb (l l' : list A) : bool :=
    forallb (λ x, inb x l') l.

End Inb.

Notation "#| l |" := (length l).

Lemma nth_error_app_r :
  ∀ A (l l' : list A) n,
    nth_error (l ++ l') (#|l| + n) = nth_error l' n.
Proof.
  intros A l l' n.
  induction l as [| a l ih] in l', n |- *.
  - reflexivity.
  - cbn. apply ih.
Qed.

Lemma nth_skipn :
  ∀ A (l : list A) x y d,
    nth (x + y) l d = nth y (skipn x l) d.
Proof.
  intros A l x y d.
  induction l as [| a l ih] in x, y |- *.
  1:{ destruct x, y. all: reflexivity. }
  destruct x, y. all: cbn. 1,2: reflexivity.
  - apply ih.
  - apply ih.
Qed.

Lemma nth_error_skipn :
  ∀ A (l : list A) x y,
    nth_error l (x + y) = nth_error (skipn x l) y.
Proof.
  intros A l x y.
  induction l as [| a l ih] in x, y |- *.
  1:{ destruct x, y. all: reflexivity. }
  destruct x, y. all: cbn. 1,2: reflexivity.
  - apply ih.
  - apply ih.
Qed.

Lemma nth_app_r :
  ∀ A (l l' : list A) d n,
    nth (#|l| + n) (l ++ l') d = nth n l' d.
Proof.
  intros A l l' d n.
  induction l as [| a l ih] in l', n |- *.
  - reflexivity.
  - cbn. apply ih.
Qed.

Definition option_bind {A B} (o : option A) (f : A → option B) :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition whenSome {A} (P : A → Prop) (o : option A) :=
  match o with
  | Some x => P x
  | None => True
  end.