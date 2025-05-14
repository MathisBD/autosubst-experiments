From Coq Require Import Utf8 List.
From GhostTT Require Import Util GAST BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping.
From GhostTT Require Export Univ TermNotations.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(** Before we define typing for vectors we need to define the gS function **)
Definition gS n :=
  reveal n (lam mGhost (Erased tnat) (Erased tnat))
    (lam mType tnat (hide (tsucc (Var 0)))).

(** We also need something which is essentially the length function
  but whose main idea is to recompute the index of a vector.
**)
Definition glength A n v :=
  tvec_elim mGhost A n v
    (* return *) (lam mGhost (Erased tnat) (
      lam mType (tvec (S ⋅ A) (Var 0)) (Erased tnat)
    )
    )
    (* vnil => *) (hide tzero)
    (* vcons => *) (lam mType A (
      lam mGhost (Erased tnat) (
        lam mType (tvec (S ⋅ S ⋅ A) (Var 0)) (
          lam mGhost (Erased tnat) (gS (Var 0))
        )
      )
    )).

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level, format "Γ  ⊢  t  :  A").

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≡  v").

Inductive conversion (Γ : context) : term → term → Prop :=

(** Computation rules **)

| conv_beta :
    ∀ m mx A t u,
      cscoping Γ A mKind →
      scoping (mx :: sc Γ) t m →
      cscoping Γ u mx →
      Γ ⊢ app (lam mx A t) u ≡ t <[ u .. ]

| reveal_hide :
    ∀ mp t P p,
      cscoping Γ t mType →
      cscoping Γ P mKind →
      cscoping Γ p mp →
      In mp [ mProp ; mGhost ] →
      Γ ⊢ reveal (hide t) P p ≡ app p t

| conv_if_true :
    ∀ m P t f,
      cscoping Γ t m →
      Γ ⊢ tif m ttrue P t f ≡ t

| conv_if_false :
    ∀ m P t f,
      cscoping Γ f m →
      Γ ⊢ tif m tfalse P t f ≡ f

| conv_nat_elim_zero :
    ∀ m P z s,
      m ≠ mKind →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tnat_elim m tzero P z s ≡ z

| conv_nat_elim_succ :
    ∀ m P z s n,
      m ≠ mKind →
      cscoping Γ n mType →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tnat_elim m (tsucc n) P z s ≡ app (app s n) (tnat_elim m n P z s)

| conv_vec_elim_nil :
    ∀ m A P z s,
      m ≠ mKind →
      cscoping Γ A mKind →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tvec_elim m A (hide tzero) (tvnil A) P z s ≡ z

| conv_vec_elim_cons :
    ∀ m A a n n' v P z s,
      m ≠ mKind →
      cscoping Γ A mKind →
      cscoping Γ a mType →
      cscoping Γ n mGhost →
      cscoping Γ n' mGhost →
      cscoping Γ v mType →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tvec_elim m A n' (tvcons a n v) P z s ≡
      app (app (app (app s a) (glength A n v)) v) (tvec_elim m A n v P z s)

(** Congruence rules **)

(** A rule to quotient away all levels of Prop, making it impredicative **)
| cong_Prop :
    ∀ i j,
      Γ ⊢ Sort mProp i ≡ Sort mProp j

| cong_Pi :
    ∀ i i' j j' m mx A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ B ≡ B' →
      ueq mx i i' →
      ueq m j j' →
      Γ ⊢ Pi i j m mx A B ≡ Pi i' j' m mx A' B'

| cong_lam :
    ∀ mx A A' t t',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ t ≡ t' →
      Γ ⊢ lam mx A t ≡ lam mx A' t'

| cong_app :
    ∀ u u' v v',
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ app u v ≡ app u' v'

| cong_Erased :
    ∀ A A',
      Γ ⊢ A ≡ A' →
      Γ ⊢ Erased A ≡ Erased A'

| cong_hide :
    ∀ u u',
      Γ ⊢ u ≡ u' →
      Γ ⊢ hide u ≡ hide u'

| cong_reveal :
    ∀ t t' P P' p p',
      Γ ⊢ t ≡ t' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ p ≡ p' →
      Γ ⊢ reveal t P p ≡ reveal t' P' p'

| cong_Reveal :
    ∀ t t' p p',
      Γ ⊢ t ≡ t' →
      Γ ⊢ p ≡ p' →
      Γ ⊢ Reveal t p ≡ Reveal t' p'

| cong_gheq :
    ∀ A A' u u' v v',
      Γ ⊢ A ≡ A' →
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ gheq A u v ≡ gheq A' u' v'

(* No need for it thanks to proof irrelevance *)
(* | cong_ghrefl :
    ∀ A A' u u',
      Γ ⊢ A ≡ A' →
      Γ ⊢ u ≡ u' →
      Γ ⊢ ghrefl A u ≡ ghrefl A' u' *)

| cong_if :
    ∀ m b P t f b' P' t' f',
      Γ ⊢ b ≡ b' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ t ≡ t' →
      Γ ⊢ f ≡ f' →
      Γ ⊢ tif m b P t f ≡ tif m b' P' t' f'

| cong_succ :
    ∀ n n',
      Γ ⊢ n ≡ n' →
      Γ ⊢ tsucc n ≡ tsucc n'

| cong_nat_elim :
    ∀ m n P z s n' P' z' s',
      Γ ⊢ n ≡ n' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ z ≡ z' →
      Γ ⊢ s ≡ s' →
      Γ ⊢ tnat_elim m n P z s ≡ tnat_elim m n' P' z' s'

| cong_vec :
    ∀ A A' n n',
      Γ ⊢ A ≡ A' →
      Γ ⊢ n ≡ n' →
      Γ ⊢ tvec A n ≡ tvec A' n'

| cong_vnil :
    ∀ A A',
      Γ ⊢ A ≡ A' →
      Γ ⊢ tvnil A ≡ tvnil A'

| cong_vcons :
    ∀ a n v a' n' v',
      Γ ⊢ a ≡ a' →
      Γ ⊢ n ≡ n' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ tvcons a n v ≡ tvcons a' n' v'

| cong_vec_elim :
    ∀ m A n v P z s A' n' v' P' z' s',
      Γ ⊢ A ≡ A' →
      Γ ⊢ n ≡ n' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ z ≡ z' →
      Γ ⊢ s ≡ s' →
      Γ ⊢ tvec_elim m A n v P z s ≡ tvec_elim m A' n' v' P' z' s'

(* Maybe not needed? *)
| cong_bot_elim :
    ∀ m A A' p p',
      Γ ⊢ A ≡ A' →
      (* Needed because syntactically we don't know p and p' are irrelevant *)
      Γ ⊢ p ≡ p' →
      Γ ⊢ bot_elim m A p ≡ bot_elim m A' p'

(** Structural rules **)

| conv_refl :
    ∀ u,
      Γ ⊢ u ≡ u

| conv_sym :
    ∀ u v,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ u

| conv_trans :
    ∀ u v w,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ w →
      Γ ⊢ u ≡ w

(** Proof irrelevance **)

| conv_irr :
    ∀ p q,
      cscoping Γ p mProp →
      cscoping Γ q mProp →
      Γ ⊢ p ≡ q

where "Γ ⊢ u ≡ v" := (conversion Γ u v).

Inductive typing (Γ : context) : term → term → Prop :=

| type_var :
    ∀ x m A,
      nth_error Γ x = Some (m, A) →
      Γ ⊢ Var x : (plus (S x)) ⋅ A

| type_sort :
    ∀ m i,
      Γ ⊢ Sort m i : Sort mKind (usup m i)

| type_pi :
    ∀ i j mx m A B,
      cscoping Γ A mKind →
      cscoping (Γ ,, (mx, A)) B mKind →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ Pi i j m mx A B : Sort m (umax mx m i j)

| type_lam :
    ∀ mx m i j A B t,
      cscoping Γ A mKind →
      cscoping (Γ ,, (mx, A)) B mKind →
      cscoping (Γ ,, (mx, A)) t m →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ,, (mx, A) ⊢ t : B →
      Γ ⊢ lam mx A t : Pi i j m mx A B

| type_app :
    ∀ i j mx m A B t u,
      cscoping (Γ ,, (mx, A)) B mKind →
      cscoping Γ t m →
      cscoping Γ u mx →
      cscoping Γ A mKind →
      Γ ⊢ t : Pi i j m mx A B →
      Γ ⊢ u : A →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ app t u : B <[ u .. ]

| type_erased :
    ∀ i A,
      cscoping Γ A mKind →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ Erased A : Sort mGhost i

| type_hide :
    ∀ i A t,
      cscoping Γ A mKind →
      cscoping Γ t mType →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ t : A →
      Γ ⊢ hide t : Erased A

| type_reveal :
    ∀ i j m A t P p,
      cscoping Γ p m →
      cscoping Γ t mGhost →
      cscoping Γ P mKind →
      cscoping Γ A mKind →
      In m [ mProp ; mGhost ] →
      Γ ⊢ t : Erased A →
      Γ ⊢ P : Erased A ⇒[ i | usup m j / mGhost | mKind ] Sort m j →
      Γ ⊢ p : Pi i j m mType A (app (S ⋅ P) (hide (Var 0))) →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ reveal t P p : app P t

| type_Reveal :
    ∀ i A t p,
      cscoping Γ t mGhost →
      cscoping Γ p mKind →
      Γ ⊢ t : Erased A →
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ A : Sort mType i →
      cscoping Γ A mKind →
      Γ ⊢ Reveal t p : Sort mProp 0

| type_toRev :
    ∀ i A t p u,
      cscoping Γ t mType →
      cscoping Γ p mKind →
      cscoping Γ u mProp →
      Γ ⊢ t : A →
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ u : app p t →
      Γ ⊢ toRev t p u : Reveal (hide t) p

| type_fromRev :
    ∀ i A t p u,
      cscoping Γ t mType →
      cscoping Γ p mKind →
      cscoping Γ u mProp →
      Γ ⊢ t : A →
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ u : Reveal (hide t) p →
      Γ ⊢ fromRev t p u : app p t

| type_gheq :
    ∀ i A u v,
      cscoping Γ A mKind →
      cscoping Γ u mGhost →
      cscoping Γ v mGhost →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ gheq A u v : Sort mProp 0

| type_ghrefl :
    ∀ i A u,
      cscoping Γ A mKind →
      cscoping Γ u mGhost →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ ghrefl A u : gheq A u u

| type_ghcast :
    ∀ i m A u v e P t,
      cscoping Γ A mKind →
      cscoping Γ P mKind →
      cscoping Γ u mGhost →
      cscoping Γ v mGhost →
      cscoping Γ t m →
      cscoping Γ e mProp →
      m ≠ mKind →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ e : gheq A u v →
      Γ ⊢ P : A ⇒[ i | usup m i / mGhost | mKind ] Sort m i →
      Γ ⊢ t : app P u →
      Γ ⊢ ghcast A u v e P t : app P v

| type_bool :
    Γ ⊢ tbool : Sort mType 0

| type_true :
    Γ ⊢ ttrue : tbool

| type_false :
    Γ ⊢ tfalse : tbool

| type_if :
    ∀ i m b P t f,
      cscoping Γ b mType →
      cscoping Γ P mKind →
      cscoping Γ t m →
      cscoping Γ f m →
      Γ ⊢ b : tbool →
      Γ ⊢ P : tbool ⇒[ 0 | usup m i / mType | mKind ] Sort m i →
      Γ ⊢ t : app P ttrue →
      Γ ⊢ f : app P tfalse →
      Γ ⊢ tif m b P t f : app P b

| type_nat :
    Γ ⊢ tnat : Sort mType 0

| type_zero :
    Γ ⊢ tzero : tnat

| type_succ :
    ∀ n,
      cscoping Γ n mType →
      Γ ⊢ n : tnat →
      Γ ⊢ tsucc n : tnat

| type_nat_elim :
    ∀ i m n P z s,
      m ≠ mKind →
      cscoping Γ n mType →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ n : tnat →
      Γ ⊢ P : tnat ⇒[ 0 | usup m i / mType | mKind ] Sort m i →
      Γ ⊢ z : app P tzero →
      Γ ⊢ s : Pi 0 i m mType tnat (app (S ⋅ P) (Var 0) ⇒[ i | i / m | m ] app (S ⋅ P) (tsucc (Var 0))) →
      Γ ⊢ tnat_elim m n P z s : app P n

| type_vec :
    ∀ A n i,
      cscoping Γ A mKind →
      cscoping Γ n mGhost →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ n : Erased tnat →
      Γ ⊢ tvec A n : Sort mType i

| type_vnil :
    ∀ A i,
      cscoping Γ A mKind →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ tvnil A : tvec A (hide tzero)

| type_vcons :
    ∀ A a n v i,
      cscoping Γ a mType →
      cscoping Γ n mGhost →
      cscoping Γ v mType →
      Γ ⊢ a : A →
      Γ ⊢ n : Erased tnat →
      Γ ⊢ v : tvec A n →
      Γ ⊢ A : Sort mType i →
      cscoping Γ A mKind →
      Γ ⊢ tvcons a n v : tvec A (gS n)

| type_vec_elim :
    ∀ i j m A n v P z s,
      m ≠ mKind →
      cscoping Γ v mType →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ v : tvec A n →
      Γ ⊢ P : Pi 0 (umax mType mKind i (usup m j)) mKind mGhost (Erased tnat) (
        tvec (S ⋅ A) (Var 0) ⇒[ i | usup m j / mType | mKind ] Sort m j
      ) →
      Γ ⊢ z : app (app P (hide tzero)) (tvnil A) →
      Γ ⊢ s : Pi i (umax mGhost m 0 (umax mType m i (umax m m j j))) m mType A (
        Pi 0 (umax mType m i (umax m m j j)) m mGhost (Erased tnat) (
          Pi i (umax m m j j) m mType (tvec (S ⋅ S ⋅ A) (Var 0)) (
            app (app (S ⋅ S ⋅ S ⋅ P) (Var 1)) (Var 0) ⇒[ j | j / m | m ]
            app (app (S ⋅ S ⋅ S ⋅ P) (gS (Var 1))) (tvcons (Var 2) (Var 1) (Var 0))
          )
        )
      ) →
      cscoping Γ n mGhost →
      cscoping Γ A mKind →
      Γ ⊢ n : Erased tnat →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ tvec_elim m A n v P z s : app (app P n) v

| type_bot :
    Γ ⊢ bot : Sort mProp 0

| type_bot_elim :
    ∀ i m A p,
      cscoping Γ A mKind →
      cscoping Γ p mProp →
      Γ ⊢ A : Sort m i →
      Γ ⊢ p : bot →
      Γ ⊢ bot_elim m A p : A

| type_conv :
    ∀ i m A B t,
      cscoping Γ A mKind →
      cscoping Γ B mKind →
      cscoping Γ t m →
      Γ ⊢ t : A →
      Γ ⊢ ε|A| ≡ ε|B| →
      Γ ⊢ B : Sort m i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (typing Γ t A).

(** Context formation **)

Inductive wf : context → Prop :=
| wf_nil : wf nil
| wf_cons :
    ∀ Γ m i A,
      wf Γ →
      cscoping Γ A mKind →
      Γ ⊢ A : Sort m i →
      wf (Γ ,, (m, A)).

Create HintDb gtt_conv discriminated.
Create HintDb gtt_type discriminated.

Hint Resolve conv_beta reveal_hide conv_if_true conv_if_false conv_nat_elim_zero
  conv_nat_elim_succ conv_vec_elim_nil conv_vec_elim_cons cong_Prop cong_Pi
  cong_lam cong_app cong_Erased cong_hide cong_reveal cong_Reveal cong_gheq
  cong_if cong_succ cong_nat_elim cong_vec cong_vnil cong_vcons cong_vec_elim
  cong_bot_elim conv_refl
: gtt_conv.

Hint Resolve type_var type_sort type_pi type_lam type_app type_erased type_hide
  type_reveal type_Reveal type_toRev type_fromRev type_gheq type_ghrefl
  type_ghcast type_bool type_true type_false type_if type_nat type_zero
  type_succ type_nat_elim type_vec type_vnil type_vcons type_vec_elim type_bot
  type_bot_elim
: gtt_type.

Ltac gconv :=
  unshelve typeclasses eauto with gtt_scope gtt_conv shelvedb ; shelve_unifiable.

Ltac gtype :=
  unshelve typeclasses eauto with gtt_scope gtt_type shelvedb ; shelve_unifiable.