From MPrototype Require Import Prelude Sig.

(** This file defines a term syntax parameterized over an arbitrary signature,
     with _admissible_ renamings and substitutions (i.e. renamings are 
     functions [nat -> nat] and substitutions are functions [nat -> term m]).
    
    We prove the main properties of substitution and renaming. *)

Section WithSig.
Context {sig : signature}.

(*********************************************************************************)
(** *** Parameterized syntax. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
#[local] Reserved Notation "'term' m" (at level 0).
#[local] Reserved Notation "'arg' ty" (at level 0, ty at level 0).
#[local] Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Terms over an abstract signature. Terms are indexed by a kind.
    Note that terms have a sort, but arguments and argument lists
    can't be assigned a unique sort in general (for instance 
    what would be the sort of [E_abase _ _] ?). *)
Inductive expr : kind -> Type :=
| (** Variable constructor. *)
  E_var {m} : nat -> term m
| (** Non-variable constructor applied to a list of arguments. *)
  E_ctor {m} : forall (c : fin (nctor m)), args (ctor_type c) -> term m
| (** Empty argument list. *)
  E_al_nil : args []
| (** Non-empty argument list. *)
  E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)
| (** Base argument (e.g. bool or string). *)
  E_abase : forall b, base_type b -> arg (AT_base b)
| (** Term argument. *)
  E_aterm {m} : term m -> arg (AT_term m)
| (** Binder argument. *)
  E_abind {ty} : forall m, arg ty -> arg (AT_bind m ty)

where "'term' m" := (expr (Kt m))
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

Derive Signature NoConfusion NoConfusionHom for expr.

(*********************************************************************************)
(** *** Induction on terms based on their size. *)
(*********************************************************************************)

(** Size of an expression. *)
Equations expr_size {k} : expr k -> nat :=
expr_size (E_var _) := 0 ;
expr_size (E_ctor c al) := S (expr_size al) ;
expr_size E_al_nil := 0 ;
expr_size (E_al_cons a al) := S (expr_size a + expr_size al) ;
expr_size (E_abase _ _) := 0 ;
expr_size (E_aterm t) := S (expr_size t) ;
expr_size (E_abind _ a) := S (expr_size a).

(** Custom induction principle on _terms_ (not on arbitrary expressions). *)
Section SizeInd.
  Context (P : forall m, term m -> Prop).

  Context (IH : forall m (t : term m), 
    (forall m' (t' : term m'), expr_size t' < expr_size t -> P m' t') -> 
    P m t).

  Lemma size_ind : forall m t, P m t.
  Proof.
  intros m t. remember (expr_size t) as n eqn:E.
  revert m t E. induction n using Wf_nat.lt_wf_ind. intros m t ->.
  apply IH. intros m' t' Hlt. eapply H ; eauto.
  Qed.
End SizeInd.

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** Vector of renamings. *)
Definition vren := vec ren nsort.

(** Equality on vectors of renamings. *)
Definition vren_eq : relation vren := vec_eq eq1.
Notation "r =ᵣ r'" := (vren_eq r r') (at level 75).

(** A vector of identity renamings. *)
Definition vrid : vren := vec_init nsort (fun _ => rid).

(** [vren_shift_point m] has [rshift] at position [m] and [rid] at other positions. *)
Definition vren_shift_point (m : fin nsort) : vren :=
  vec_init nsort (fun m' => if eq_dec m m' then rshift else rid).

(** Lift a vector of renamings through a binder for sort [m]. *)
Definition vrup (m : fin nsort) (r : vren) : vren :=
  vec_mapi (fun m' r_m' => if eq_dec m m' then rup r_m' else r_m') r.

(** Apply a vector of renamings to an expression. *)
Equations rename {k} (r : vren) (t : expr k) : expr k :=
rename r (@E_var m i) := E_var (vec_nth r m i) ;
rename r (E_ctor c al) := E_ctor c (rename r al) ;
rename r E_al_nil := E_al_nil ;
rename r (E_al_cons a al) := E_al_cons (rename r a) (rename r al) ;
rename r (E_abase b x) := E_abase b x ;
rename r (E_aterm t) := E_aterm (rename r t) ;
rename r (E_abind m a) := E_abind m (rename (vrup m r) a).

(** Compose of two vectors of renamings. *)
Definition vrcomp (r1 r2 : vren) : vren :=
  vec_map2 rcomp r1 r2.
  
(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A single substitution which yields terms of sort [m]. *)
Definition subst m := nat -> term  m.

(** A vector of substitutions. *)
Definition vsubst := hvec nsort subst.

(** Equality on vectors of substitutions. *)
Definition vsubst_eq : relation vsubst := hvec_eq (fun _ => eq1).
Notation "s =ₛ s'" := (vsubst_eq s s') (at level 75).

(** The identity substitution. *)
Definition sid {m} : subst m := fun i => E_var i.

(** A vector of identity substitutions. *)
Definition vsid : vsubst := 
  hvec_init nsort (fun _ => sid).

(** [sshift] shifts indices by one. *)
Definition sshift {m} : subst m := 
  fun i => E_var (S i).

(** Cons a term with a substitution. *)
Equations scons {m} (t : term m) (s : subst m) : subst m :=
scons t s 0 := t ;
scons t s (S i) := s i.

(** Compose of a renaming with a substitution. *)
Definition rscomp {m} (r : ren) (s : subst m) : subst m := 
  fun i => s (r i).

(** Compose of a substitution with a vector of renamings. *)
Definition svrcomp {m} (s : subst m) (r : vren) : subst m := 
  fun i => rename r (s i).

(** Lift a vector of substitutions through a binder of sort [m].*)
Definition vsup (m : fin nsort) (s : vsubst) : vsubst :=
  let r := vren_shift_point m in 
  hvec_mapi 
    (fun m' s_m' => 
      if eq_dec m m' 
      then scons (E_var 0) (svrcomp s_m' r) 
      else svrcomp s_m' r) s.

(** Apply a vector of substitutions to an expression. *)
Equations substitute {k} (s : vsubst) (t : expr k) : expr k :=
substitute s (@E_var m i) := hvec_nth s m i ;
substitute s (E_ctor c al) := E_ctor c (substitute s al) ;
substitute s E_al_nil := E_al_nil ;
substitute s (E_al_cons a al) := E_al_cons (substitute s a) (substitute s al) ;
substitute s (E_abase b x) := E_abase b x ;
substitute s (E_aterm t) := E_aterm (substitute s t) ;
substitute s (E_abind m a) := E_abind m (substitute (vsup m s) a).

(** Compose of a substitution with a vector of substitutions. *)
Definition svscomp {m} (s1 : subst m) (s2 : vsubst) : subst m :=
  fun i => substitute s2 (s1 i).

(** Compose of two vectors of substitutions. *)
Definition vscomp (s1 s2 : vsubst) : vsubst :=
  hvec_mapi (fun _ s1_m => svscomp s1_m s2) s1.

(** Compose of a vector of renamings with a vector of substitutions. *)
Definition vrvscomp (r : vren) (s : vsubst) : vsubst := 
  hvec_mapi2 (@rscomp) (hvec_of_vec r) s.  

(** Compose of a vector of substitutions with a vector of renamings. *)
Definition vsvrcomp (s : vsubst) (r : vren) : vsubst := 
  hvec_mapi (fun _ s_m => svrcomp s_m r) s.
  
(*********************************************************************************)
(** *** Setoid Rewrite lemmas. *)
(*********************************************************************************)

#[export] Instance vrup_proper : 
  Proper (eq ==> vren_eq ==> vren_eq) vrup.
Proof.
intros m ? <- r r' Hr. unfold vrup. apply (vec_mapi_proper eq1) ; [|assumption].
intros m1 m2 -> r1 r2 ?. destruct (eq_dec m m2) ; [|assumption].
now setoid_rewrite H.
Qed.

#[export] Instance rename_proper k : 
  Proper (vren_eq ==> eq ==> eq) (@rename k).
Proof.
intros rv rv' Hr t _ <-. induction t in rv, rv', Hr |- * ; simp rename.
all: try solve [ f_equal ; auto ].
- now rewrite Hr. 
- f_equal. apply IHt. now rewrite Hr.
Qed.

#[export] Instance vrcomp_proper : 
  Proper (vren_eq ==> vren_eq ==> vren_eq) vrcomp.
Proof. intros r1 r1' H1 r2 r2' H2. unfold vrcomp. now rewrite H1, H2. Qed.

#[export] Instance svrcomp_proper m : 
  Proper (eq1 ==> vren_eq ==> eq1) (@svrcomp m).
Proof. intros s s' Hs r r' Hr i. unfold svrcomp. now rewrite Hr, Hs. Qed.

#[export] Instance rscomp_proper m : 
  Proper (eq1 ==> eq1 ==> eq1) (@rscomp m).
Proof. intros r r' Hr s s' Hs i. unfold rscomp. now rewrite Hr, Hs. Qed.

#[export] Instance scons_proper m : 
  Proper (eq ==> eq1 ==> eq1) (@scons m).
Proof. intros t ? <- s s' Hs i. unfold scons. now destruct i. Qed.

#[export] Instance vsup_proper : 
  Proper (eq ==> vsubst_eq ==> vsubst_eq) vsup.
Proof.
intros m ? <- s s' Hs. unfold vsup. apply (hvec_mapi_proper (fun _ => eq1)).
- clear. intros i s s' Hs. destruct (eq_dec m i).
  + subst. now rewrite Hs.
  + now rewrite Hs.
- assumption.
Qed. 

#[export] Instance substitute_proper k : 
  Proper (vsubst_eq ==> eq ==> eq) (@substitute k).
Proof.
intros s s' Hs t ? <-. induction t in s, s', Hs |- * ; simp substitute.
all: try solve [ f_equal ; auto ].
- apply Hs.
- f_equal. apply IHt. now rewrite Hs.
Qed.

#[export] Instance svscomp_proper m : 
  Proper (eq1 ==> vsubst_eq ==> eq1) (@svscomp m).
Proof. intros s1 s1' H1 s2 s2' H2 i. unfold svscomp. now rewrite H1, H2. Qed.

#[export] Instance vscomp_proper : 
  Proper (vsubst_eq ==> vsubst_eq ==> vsubst_eq) vscomp.
Proof.
intros s1 s1' H1 s2 s2' H2. unfold vscomp. apply (hvec_mapi_proper (fun _ => eq1)).
- clear -H2. intros i s s' Hs. now rewrite Hs, H2.
- apply H1.
Qed.

#[export] Instance vrvscomp_proper : 
  Proper (vren_eq ==> vsubst_eq ==> vsubst_eq) vrvscomp.
Proof. 
intros r r' Hr s s' Hs. unfold vrvscomp. apply (hvec_mapi2_proper (fun _ => eq1) (fun _ => eq1)).
- clear. intros i r r' Hr s s' Hs. now rewrite Hr, Hs.
- now rewrite Hr.
- exact Hs.
Qed.

#[export] Instance vsvrcomp_proper : 
  Proper (vsubst_eq ==> vren_eq ==> vsubst_eq) vsvrcomp.
Proof. 
intros s s' Hs r r' Hr. unfold vsvrcomp. apply (hvec_mapi_proper (fun _ => eq1)).
- clear -Hr. intros i s s' ->. now rewrite Hr.
- exact Hs.
Qed.

(*********************************************************************************)
(** *** Pushing [vec_nth] and [hvec_nth] inside expressions. *)
(*********************************************************************************)

Lemma vec_nth_vrid m : 
  vec_nth vrid m =₁ rid.
Proof. intros i. unfold vrid. now simp vec_nth. Qed.
#[local] Hint Rewrite vec_nth_vrid : vec_nth.

Lemma vec_nth_vren_shift_point m m' : 
  vec_nth (vren_shift_point m) m' =₁ if eq_dec m m' then rshift else rid.
Proof. intros i. unfold vren_shift_point. now simp vec_nth. Qed.
#[local] Hint Rewrite vec_nth_vren_shift_point : vec_nth. 

Lemma vec_nth_vrup r m m' : 
  vec_nth (vrup m r) m' =₁ if eq_dec m m' then rup (vec_nth r m') else vec_nth r m'.
Proof. intros i. unfold vrup. now simp vec_nth. Qed.
#[local] Hint Rewrite vec_nth_vrup : vec_nth.

Lemma vec_nth_vrcomp r1 r2 m : 
  vec_nth (vrcomp r1 r2) m =₁ rcomp (vec_nth r1 m) (vec_nth r2 m).
Proof. intros i. unfold vrcomp, rcomp. now simp vec_nth. Qed.
#[local] Hint Rewrite vec_nth_vrcomp : vec_nth.

Lemma hvec_nth_vsid m : 
  hvec_nth vsid m =₁ sid.
Proof. intros i. unfold vsid. now simp hvec_nth. Qed.
#[local] Hint Rewrite hvec_nth_vsid : hvec_nth.

Lemma hvec_nth_vsup s m m' : 
  hvec_nth (vsup m s) m' =₁ 
    if eq_dec m m' 
    then scons (E_var 0) (svrcomp (hvec_nth s m') (vren_shift_point m))
    else svrcomp (hvec_nth s m') (vren_shift_point m).
Proof. intros i. unfold vsup. now simp hvec_nth. Qed.
#[local] Hint Rewrite hvec_nth_vsup : hvec_nth.

Lemma hvec_nth_vscomp s1 s2 m : 
  hvec_nth (vscomp s1 s2) m =₁ svscomp (hvec_nth s1 m) s2.
Proof. intros i. unfold vscomp. now simp hvec_nth. Qed.
#[local] Hint Rewrite hvec_nth_vscomp : hvec_nth.

Lemma hvec_nth_vrvscomp r s m : 
  hvec_nth (vrvscomp r s) m =₁ rscomp (vec_nth r m) (hvec_nth s m).
Proof. intros i. unfold vrvscomp. now simp hvec_nth. Qed.
#[local] Hint Rewrite hvec_nth_vrvscomp : hvec_nth.

Lemma hvec_nth_vsvrcomp s r m : 
  hvec_nth (vsvrcomp s r) m =₁ svrcomp (hvec_nth s m) r.
Proof. intros i. unfold vsvrcomp. now simp hvec_nth. Qed.
#[local] Hint Rewrite hvec_nth_vsvrcomp : hvec_nth.

(*********************************************************************************)
(** *** Properties of renamings and substitutions. *)
(*********************************************************************************)

Lemma rid_rcons : 
  rcons 0 rshift =₁ rid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma sid_scons {m} : 
  scons (E_var 0) (@sshift m) =₁ sid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma rcomp_rcons_distrib i (r1 r2 : ren) :
  rcomp (rcons i r1) r2 =₁ rcons (r2 i) (rcomp r1 r2).
Proof. intros [|i'] ; reflexivity. Qed.

Lemma scomp_scons_distrib {m} (t : term m) (s1 : subst m) (s2 : vsubst) :
  svscomp (scons t s1) s2 =₁ scons (substitute s2 t) (svscomp s1 s2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma rshift_rcons (i : nat) (r : ren) : 
  rcomp rshift (rcons i r) =₁ r.
Proof. reflexivity. Qed.
    
(*Lemma sshift_scons m (t : term m) (s : subst m) : 
  scomp sshift (scons t s) =₁ s.
Proof. reflexivity. Qed.*)

Lemma rcomp_id_l (r : ren) : rcomp rid r =₁ r.
Proof. reflexivity. Qed.

Lemma rcomp_id_r (r : ren) : rcomp r rid =₁ r.
Proof. reflexivity. Qed.

Lemma rcomp_assoc (r1 r2 r3 : ren) : 
  rcomp (rcomp r1 r2) r3 =₁ rcomp r1 (rcomp r2 r3).
Proof. reflexivity. Qed.

Lemma rup_id : rup rid =₁ rid.
Proof. intros [|] ; reflexivity. Qed.

Lemma comp_rup_rup (r1 r2 : ren) : 
  rcomp (rup r1) (rup r2) =₁ rup (rcomp r1 r2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma vrup_id {m} : vrup m vrid =ᵣ vrid.
Proof. 
intros m'. simp vec_nth. destruct (eq_dec m m') ; simp vec_nth.
- now rewrite rup_id.
- reflexivity.
Qed.

Lemma comp_vrup_vrup {m} r1 r2 : 
  vrcomp (vrup m r1) (vrup m r2) =ᵣ vrup m (vrcomp r1 r2).
Proof.
intros m'. simp vec_nth. destruct (eq_dec m m') ; simp vec_nth.
- subst. now rewrite comp_rup_rup.
- reflexivity.
Qed. 

Lemma rename_id {k} (t : expr k) : rename vrid t = t.
Proof.
induction t ; simp rename vec_nth ; f_equal ; auto.
now rewrite vrup_id, IHt.
Qed.

Lemma vsup_id {m} : vsup m vsid =ₛ vsid.
Proof. 
intros m'. simp hvec_nth. destruct (eq_dec m m') ; subst ; setoid_rewrite (hvec_nth_vsid m').
- intros i. destruct i ; cbn ; [reflexivity|]. simp vec_nth. 
  now rewrite eq_dec_refl.
- intros i. unfold svrcomp. cbn. simp vec_nth. destruct (eq_dec m m').
  + now apply n in e. 
  + reflexivity.
Qed.

Lemma substitute_id {k} (t : expr k) : substitute vsid t = t.
Proof.
induction t ; simp substitute hvec_nth in * ; f_equal ; auto.
now rewrite vsup_id. 
Qed.

Lemma rename_rename {k} (t : expr k) (r1 r2 : vren) : 
  rename r2 (rename r1 t) = rename (vrcomp r1 r2) t.
Proof.
induction t in r1, r2 |- * ; simp rename vec_nth in * ; f_equal ; auto.
now rewrite IHt, comp_vrup_vrup.
Qed.

Lemma comp_vrup_vsup {m} r s : 
  vrvscomp (vrup m r) (vsup m s) =ₛ vsup m (vrvscomp r s).
Proof.
intros m'. simp hvec_nth vec_nth. destruct (eq_dec m m') ; simp hvec_nth.
- subst. intros [|] ; reflexivity.
- reflexivity.
Qed. 

Lemma substitute_rename {k} (t : expr k) (r : vren) (s : vsubst) : 
  substitute s (rename r t) = substitute (vrvscomp r s) t.
Proof.
induction t in r, s |- * ; simp rename substitute hvec_nth ; f_equal ; auto.
now rewrite IHt, comp_vrup_vsup.
Qed.

Lemma comp_vsup_vrup {m} s r :
  vsvrcomp (vsup m s) (vrup m r) =ₛ vsup m (vsvrcomp s r).
Proof.
intros m'. simp hvec_nth. destruct (eq_dec m m') ; simp hvec_nth.
- subst. intros [|i] ; cbn ; simp vec_nth.
  + rewrite eq_dec_refl. reflexivity.
  + cbv [svrcomp]. rewrite !rename_rename. apply rename_proper ; [|reflexivity].
    clear. intros m. simp vec_nth.
    destruct (eq_dec m' m) ; subst ; reflexivity.
- intros i. cbv [svrcomp]. rewrite !rename_rename. apply rename_proper ; [|reflexivity].
  clear. intros m''. simp vec_nth.
  destruct (eq_dec m m'') ; subst ; reflexivity.
Qed.

Lemma rename_substitute {k} (t : expr k) (s : vsubst) (r : vren) : 
  rename r (substitute s t) = substitute (vsvrcomp s r) t.
Proof.
induction t in s, r |- * ; simp rename substitute hvec_nth in * ; f_equal ; auto.
now rewrite IHt, comp_vsup_vrup.
Qed.

Lemma comp_vsup_vsup {m} s1 s2 :
  vscomp (vsup m s1) (vsup m s2) =ₛ vsup m (vscomp s1 s2).
Proof.
intros m'. simp hvec_nth. destruct (eq_dec m m') ; simp hvec_nth.
- subst. intros [|i] ; cbn.
  + simp hvec_nth. rewrite eq_dec_refl. reflexivity.
  + cbv [svrcomp svscomp]. rewrite substitute_rename, rename_substitute.
    apply substitute_proper ; [|reflexivity]. clear. intros m. 
    simp hvec_nth vec_nth. destruct (eq_dec m' m) ; subst ; reflexivity.
- intros i. cbv [svscomp svrcomp]. rewrite substitute_rename, rename_substitute. 
  apply substitute_proper ; [|reflexivity]. clear. intros m''. simp hvec_nth vec_nth.
  destruct (eq_dec m m'') ; subst ; reflexivity.
Qed.

Lemma substitute_substitute {k} (t : expr k) (s1 s2 : vsubst) : 
  substitute s2 (substitute s1 t) = substitute (vscomp s1 s2) t.
Proof.
induction t in s1, s2 |- * ; simp substitute hvec_nth ; f_equal ; auto.
now rewrite IHt, comp_vsup_vsup.
Qed.

(*Lemma scomp_sid_l (s : subst) : scomp sid s =₁ s.
Proof. reflexivity. Qed.

Lemma scomp_sid_r (s : subst) : scomp s sid =₁ s.
Proof. intros i. cbv [scomp]. now rewrite subst_sid. Qed.

Lemma scomp_assoc (s1 s2 s3 : subst) : 
  scomp (scomp s1 s2) s3 =₁ scomp s1 (scomp s2 s3).
Proof. intros i. cbv [scomp]. now rewrite subst_subst. Qed.*)

(*Lemma ren_is_subst {k} (t : expr k) (r : vren) : 
  rename r t = substitute (fun vrscomp r E_var) t.
Proof.
funelim (rename r t) ; simp rename substitute ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; reflexivity.
Qed.

Lemma rshift_sshift {k} (t : expr k) : 
  rename rshift t = substitute sshift t.
Proof. rewrite ren_is_subst. reflexivity. Qed.
    
Lemma up_subst_alt (s : subst) :
  up_subst s =₁ scons (E_var 0) (scomp s sshift).
Proof.
simp up_subst. apply scons_proper ; auto.
intros i. cbv [scomp srcomp]. now rewrite rshift_sshift.
Qed.*)

End WithSig.