From Prototype Require Export All.

(*********************************************************************************)
(** *** Generate all operations and lemmas. *)
(*********************************************************************************)

Autosubst Generate 
{{
  expr(var) : Type

  (* Types. *)
  arr : expr -> expr -> expr 
  all : (bind expr in expr) -> expr 

  (* Terms. *)
  app : expr -> expr -> expr 
  tapp : expr -> expr -> expr 
  vt : expr -> expr 

  (* Values. *)
  lam : expr -> (bind expr in expr) -> expr 
  tlam : (bind expr in expr) -> expr
}}.

Derive NoConfusion NoConfusionHom for expr.

Inductive sort := Sty | Stm | Svl. 
Derive NoConfusion for sort.

(*********************************************************************************)
(** *** Triggers for [rasimpl]. *)
(*********************************************************************************)

(** Trigger [rasimpl] on [rename _ _]. *)
Lemma rasimpl_trigger_rename (r : ren) (t res : expr) :
  TermSimplification (rename r t) res -> rename r t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_rename : asimpl_topdown.

(** Trigger [rasimpl] on [substitute _ _]. *)
Lemma rasimpl_trigger_substitute (s : subst) (t res : expr) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_substitute : asimpl_topdown.

(*********************************************************************************)
(** *** Scoping for terms. *)
(*********************************************************************************)

Definition scope := list sort.

(** Scoping as a proposition. *)
Inductive scoping : scope -> expr -> sort -> Prop :=

| scoping_var Γ i s :
    nth_error Γ i = Some s -> scoping Γ (var i) s

| scoping_arr Γ t1 t2 : 
    scoping Γ t1 Sty -> scoping Γ t2 Sty -> scoping Γ (arr t1 t2) Sty

| scoping_all Γ t : 
    scoping (Sty :: Γ) t Sty -> scoping Γ (all t) Sty

| scoping_app Γ t1 t2 :
    scoping Γ t1 Stm -> scoping Γ t2 Stm -> scoping Γ (app t1 t2) Stm

| scoping_tapp Γ t1 t2 : 
    scoping Γ t1 Stm -> scoping Γ t2 Sty -> scoping Γ (tapp t1 t2) Stm

| scoping_vt Γ t : 
    scoping Γ t Svl -> scoping Γ (vt t) Stm

| scoping_lam Γ t1 t2 : 
    scoping Γ t1 Sty -> scoping (Svl :: Γ) t2 Stm -> scoping Γ (lam t1 t2) Svl

| scoping_tlam Γ t :
    scoping (Sty :: Γ) t Stm -> scoping Γ (tlam t) Svl.

Derive Signature for scoping.

(** Trigger [rasimpl] on [scoping]. *)
Lemma rasimpl_trigger_scoping Γ t1 t2 m :
  TermSimplification t1 t2 ->
    scoping Γ t1 m <-> scoping Γ t2 m.
Proof. intros H. now rewrite (@term_simplification _ t1 t2 H). Qed.
#[export] Hint Rewrite -> rasimpl_trigger_scoping : asimpl_outermost.

(** Read the sort of a (well-scoped) expression. *)
Definition read_sort (Γ : scope) (t : expr) : sort :=
  match t with 
  | var i => 
    (* We use a dummy sort in case [i] is not in scope. *)
    nth i Γ Sty
  | arr _ _ | all _ => Sty 
  | app _ _ | tapp _ _ | vt _ => Stm
  | lam _ _ | tlam _ => Svl
  end.

(** Relation between the two notions of scoping. *)
Lemma read_sort_spec Γ t s : 
  scoping Γ t s -> read_sort Γ t = s.
Proof. intros H. destruct H ; cbn ; try reflexivity. now apply nth_error_nth. Qed.

(** Consequence: scoping is functional. *)
Lemma scoping_functional Γ t s1 s2 :
  scoping Γ t s1 ->
  scoping Γ t s2 ->
  s1 = s2.
Proof.
intros H1 H2. transitivity (read_sort Γ t).
- symmetry. now apply read_sort_spec.
- now apply read_sort_spec.
Qed. 

(*********************************************************************************)
(** *** Scoping for renamings. *)
(*********************************************************************************)

(** [rscoping Γ r Δ] states that [r] takes inputs in [Δ] and has outputs in [Γ]. *)
Definition rscoping (Γ : scope) (r : ren) (Δ : scope) : Prop :=
  forall i mi,
    nth_error Δ i = Some mi ->
    nth_error Γ (r i) = Some mi.

#[export] Instance rscoping_proper : 
  Proper (eq ==> point_eq ==> eq ==> iff) rscoping.
Proof.
intros ? Γ -> r1 r2 Hr ? t ->. split.
- intros H i mi Hi. rewrite <-Hr. now apply H.
- intros H i mi Hi. rewrite Hr. now apply H.
Qed.

(** Trigger [rasimpl] on [rscoping]. *)
Lemma rasimpl_trigger_rscoping Γ r1 r2 Δ :
  RenSimplification r1 r2 ->
    rscoping Γ r1 Δ <-> rscoping Γ r2 Δ.
Proof. intros H. now rewrite ren_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_rscoping : asimpl_outermost.

Lemma rscoping_rid Γ :
  rscoping Γ rid Γ.
Proof. intros i mi H. assumption. Qed.
#[export] Hint Resolve rscoping_rid : scoping.

Lemma rscoping_rshift Γ m :
  rscoping (m :: Γ) rshift Γ.
Proof. intros i mi H. now cbn. Qed.
#[export] Hint Resolve rscoping_rshift : scoping.

Lemma rscoping_rcons Γ Δ i mi r : 
  nth_error Γ i = Some mi -> rscoping Γ r Δ -> rscoping Γ (rcons i r) (mi :: Δ).
Proof.
intros Hi Hr x mx Hx. destruct x ; cbn in *.
- depelim Hx. assumption.
- apply Hr. assumption.
Qed.  
#[export] Hint Resolve rscoping_rcons : scoping.

Lemma rscoping_rcomp Γ Δ Ε r1 r2 :
  rscoping Δ r1 Ε -> rscoping Γ r2 Δ -> rscoping Γ (rcomp r1 r2) Ε.
Proof. intros H1 H2 i mi Hi. apply H2. apply H1. assumption. Qed.
#[export] Hint Resolve rscoping_rcomp : scoping.

Lemma rscoping_up_ren Γ Δ r m :
  rscoping Γ r Δ -> rscoping (m :: Γ) (up_ren r) (m :: Δ).
Proof. unfold up_ren. auto with scoping. Qed.
#[export] Hint Resolve rscoping_up_ren : scoping.

(** Renaming preserves the scope. *)
Lemma rscoping_rename Γ Δ r t st :
  rscoping Γ r Δ ->
  scoping Δ t st ->
  scoping Γ (rename r t) st.
Proof.
intros Hr Ht. induction Ht in Γ, r, Hr |- *.
all: solve [ rasimpl ; constructor ; auto with scoping ].
Qed.
#[export] Hint Resolve rscoping_rename : scoping.

(*********************************************************************************)
(** *** Scoping for substitutions. *)
(*********************************************************************************)

(** [sscoping Γ s Δ] states that [s] takes inputs in [Δ] and has outputs in [Γ]. *)
Inductive sscoping (Γ : scope) : subst -> scope -> Prop :=
| sscoping_nil s : sscoping Γ s []
| sscoping_cons Δ s m :
    sscoping Γ (scomp sshift s) Δ ->
    scoping Γ (s 0) m ->
    sscoping Γ s (m :: Δ).

#[export] Instance sscoping_proper : 
  Proper (eq ==> point_eq ==> eq ==> iff) sscoping.
Proof.
intros ? Γ -> s1 s2 Hs ? t ->. split ; intros H.
- induction H in s2, Hs |- * ; constructor.
  + apply IHsscoping. now apply congr_scomp.
  + now rewrite <-Hs.    
- induction H in s1, Hs |- * ; constructor.
  + apply IHsscoping. now apply congr_scomp.
  + now rewrite Hs.    
Qed.

(** Trigger [rasimpl] on [sscoping]. *)
Lemma rasimpl_trigger_sscoping Γ s1 s2 Δ :
  SubstSimplification s1 s2 ->
    sscoping Γ s1 Δ <-> sscoping Γ s2 Δ.
Proof. intros H. now rewrite subst_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_sscoping : asimpl_outermost.

Lemma sscoping_sshift_r Γ Δ s m :
  sscoping Γ s Δ -> sscoping (m :: Γ) (scomp s sshift) Δ.
Proof.
intros H. induction H.
- constructor.
- constructor.
  + assumption.
  + assert (scomp s sshift 0 = rename rshift (s 0)) as -> by now rasimpl. 
    eapply rscoping_rename ; eauto with scoping.
Qed.
#[export] Hint Resolve sscoping_sshift_r : scoping.

(** Substituting preserves the scope. *)
Lemma sscoping_substitute Γ Δ s t m :
  sscoping Γ s Δ ->
  scoping Δ t m ->
  scoping Γ (substitute s t) m.
Proof.
intros Hs Ht.
induction Ht in Γ, s, Hs |- *.
all: rasimpl.
all: try solve [ econstructor ; eauto ].
- induction Hs in i, H |- *.
  + now destruct i.
  + destruct i ; cbn in *.
    * depelim H. assumption.
    * apply IHHs. assumption.   
- constructor.
  apply IHHt. constructor.
  + rasimpl. now apply sscoping_sshift_r. 
  + rasimpl. constructor. reflexivity.
- constructor.
  + eauto.
  + apply IHHt2. constructor.
    * rasimpl. now apply sscoping_sshift_r. 
    * rasimpl. constructor. reflexivity.
- constructor. apply IHHt. constructor.
  + rasimpl. now apply sscoping_sshift_r.
  + rasimpl. constructor. reflexivity.   
Qed.
#[export] Hint Resolve sscoping_substitute : scoping.

Lemma sscoping_sid Γ :
  sscoping Γ sid Γ.
Proof.
induction Γ.
- constructor.
- constructor. 
  + rasimpl. apply sscoping_sshift_r with (m := a) in IHΓ. rasimpl in IHΓ. assumption.
  + rasimpl. constructor. reflexivity.
Qed.      

Lemma sscoping_up_subst Γ Δ m s :
  sscoping Γ s Δ ->
  sscoping (m :: Γ) (up_subst s) (m :: Δ).
Proof.
intros H. constructor.
- rasimpl. eauto with scoping.
- rasimpl. now constructor.
Qed.


(*Inductive ty_view : scoping -> expr -> Type :=
| ty_view_var i : ty_view (scoping_var Γ i Sty p) (var i) 
| ty_view_arr t1 t2 : ty_view (arr t1 t2)
| ty_view_all t : ty_view (all t).

Definition build_ty_view (Γ : scope) (t : expr) (s : scoping Γ t Sty) : ty_view t.
depelim s ; constructor.
Defined.

Equations ty_size Γ t (s : scoping Γ t Sty) : nat :=
ty_size Γ t s with ty_view Γ t s :=
ty_size Γ (var i) s (ty_view_var _) := 0 ;
ty_size Γ (arr t1 t2)  (ty_view_arr _ _) := S (ty_size s1 + ty_size s2) ;

ty_size (scoping_var _ _ _ _) := 0 ;
ty_size (scoping_arr _ t1 t2 s1 s2) := S (ty_size s1 + ty_size s2) ;
ty_size (scoping_all _ t s) := S (ty_size s).*)

(*********************************************************************************)
(** *** Triggers. *)
(*********************************************************************************)

(*(** Trigger [rasimpl] on [rename _ _]. *)
Lemma autosubst_simpl_term_rename (r : ren) (t res : term) :
  TermSimplification (rename r t) res -> rename r t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_rename : asimpl_topdown.

(** Trigger [rasimpl] on [substitute _ _]. *)
Lemma autosubst_simpl_term_substitute (s : subst) (t res : term) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl_topdown.

Axiom F : subst -> term.

(** Trigger [rasimpl] on a substitution occuring inside [F _]. *)
(*Lemma autosubst_simpl_F (s res : subst) :
  SubstSimplification s res -> F s = F res.
Proof. Admitted.
#[export] Hint Rewrite -> autosubst_simpl_F : asimpl_outermost.*)

Axiom r : ren.
Axiom s : subst.
Axiom t : term.
Lemma test : substitute (scomp s (scons (substitute (rscomp r s) t) s)) t = t.
Proof. rasimpl.
Admitted.*)