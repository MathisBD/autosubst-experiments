(** Scoping

  Stating that all variables are in a given scope, and in a given mode.

**)

From Coq Require Import Utf8 List.
From GhostTT Require Import GAST BasicAST SubstNotations ContextDecl CastRemoval.

Import ListNotations.

Set Default Goal Selector "!".

Inductive scoping (Γ : scope) : term → mode → Prop :=

| scope_var :
    ∀ x m,
      nth_error Γ x = Some m →
      scoping Γ (Var x) m

| scpoe_sort :
    ∀ m i,
      scoping Γ (Sort m i) mKind

| scope_pi :
    ∀ i j mx m A B,
      scoping Γ A mKind →
      scoping (mx :: Γ) B mKind →
      scoping Γ (Pi i j m mx A B) mKind

| scope_lam :
    ∀ mx m A t,
      scoping Γ A mKind →
      scoping (mx :: Γ) t m →
      scoping Γ (lam mx A t) m

| scope_app :
    ∀ mx m t u,
      scoping Γ t m →
      scoping Γ u mx →
      scoping Γ (app t u) m

| scope_erased :
    ∀ A,
      scoping Γ A mKind →
      scoping Γ (Erased A) mKind

| scope_hide :
    ∀ t,
      scoping Γ t mType →
      scoping Γ (hide t) mGhost

| scope_reveal :
    ∀ m t P p,
      In m [ mProp ; mGhost ] →
      scoping Γ t mGhost →
      scoping Γ P mKind →
      scoping Γ p m →
      scoping Γ (reveal t P p) m

| scope_Reveal :
    ∀ t p,
      scoping Γ t mGhost →
      scoping Γ p mKind →
      scoping Γ (Reveal t p) mKind

| scope_toRev :
    ∀ t p u,
      scoping Γ t mType →
      scoping Γ p mKind →
      scoping Γ u mProp →
      scoping Γ (toRev t p u) mProp

| scope_fromRev :
    ∀ t p u,
      scoping Γ t mType →
      scoping Γ p mKind →
      scoping Γ u mProp →
      scoping Γ (fromRev t p u) mProp

| scope_gheq :
    ∀ A u v,
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ v mGhost →
      scoping Γ (gheq A u v) mKind

| scope_ghrefl :
    ∀ A u,
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ (ghrefl A u) mProp

| scope_ghcast :
    ∀ m A u v e P t,
      m ≠ mKind →
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ v mGhost →
      scoping Γ e mProp →
      scoping Γ P mKind →
      scoping Γ t m →
      scoping Γ (ghcast A u v e P t) m

| scope_bool :
    scoping Γ tbool mKind

| scope_true :
    scoping Γ ttrue mType

| scope_false :
    scoping Γ tfalse mType

| scope_if :
    ∀ m b P t f,
      scoping Γ b mType →
      scoping Γ P mKind →
      scoping Γ t m →
      scoping Γ f m →
      scoping Γ (tif m b P t f) m

| scope_nat :
    scoping Γ tnat mKind

| scope_zero :
    scoping Γ tzero mType

| scope_succ :
    ∀ n,
      scoping Γ n mType →
      scoping Γ (tsucc n) mType

| scope_nat_elim :
    ∀ m n P z s,
      m ≠ mKind →
      scoping Γ n mType →
      scoping Γ P mKind →
      scoping Γ z m →
      scoping Γ s m →
      scoping Γ (tnat_elim m n P z s) m

| scope_vec :
    ∀ A n,
      scoping Γ A mKind →
      scoping Γ n mGhost →
      scoping Γ (tvec A n) mKind

| scope_vnil :
    ∀ A,
      scoping Γ A mKind →
      scoping Γ (tvnil A) mType

| scope_vcons :
    ∀ a n v,
      scoping Γ a mType →
      scoping Γ n mGhost →
      scoping Γ v mType →
      scoping Γ (tvcons a n v) mType

| scope_vec_elim :
    ∀ m A n v P z s,
      m ≠ mKind →
      scoping Γ A mKind →
      scoping Γ n mGhost →
      scoping Γ v mType →
      scoping Γ P mKind →
      scoping Γ z m →
      scoping Γ s m →
      scoping Γ (tvec_elim m A n v P z s) m

| scope_bot :
    scoping Γ bot mKind

| scope_bot_elim :
    ∀ m A p,
      scoping Γ A mKind →
      scoping Γ p mProp →
      scoping Γ (bot_elim m A p) m
.

Notation cscoping Γ := (scoping (sc Γ)).

Create HintDb gtt_scope discriminated.

Hint Constructors scoping : gtt_scope.

Ltac gscope :=
  unshelve typeclasses eauto with gtt_scope shelvedb ; shelve_unifiable.