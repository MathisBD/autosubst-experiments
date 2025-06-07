From Prototype Require Import MPrelude MSig.

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
  E_ctor {m} : forall (c : ctor m), args (ctor_type c) -> term m
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
(** *** Induction on expressions based on their size. *)
(*********************************************************************************)

(*(** Size of expressions. *)
Equations expr_size {k} : expr k -> nat :=
expr_size (E_var _) := 0 ;
expr_size (E_ctor c al) := S (expr_size al) ;
expr_size E_al_nil := 0 ;
expr_size (E_al_cons a al) := S (expr_size a + expr_size al) ;
expr_size (E_abase _ _) := 0 ;
expr_size (E_aterm t) := S (expr_size t) ;
expr_size (E_abind _ a) := S (expr_size a).

Section SizeInd.
  Context (P : forall k, expr k -> Prop).

  Context (IH : forall s (t : term s), 
    (forall s' (t' : term s'), expr_size t' < expr_size t -> P s' t') -> 
    P s t).

  Lemma size_ind : forall s t, P s t.
  Proof.
  intros s t. remember (term_size t) as n eqn:E.
  revert s t E. induction n using Wf_nat.lt_wf_ind. intros s t ->.
  apply IH. intros s' t' Hlt. eapply H ; eauto.
  Qed.
End SizeInd.*)

(** Notation for left to right function composition. *)
(*Notation "f >> g" := (fun i => g (f i)) (at level 30).*)

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** Vector of renamings. *)
Definition vren := sort -> ren.

(** A vector of identity renamings. *)
Definition vrid : vren := fun _ => rid.

(** [vren_shift_point m] has [rshift] at position [m] and [rid] at other positions. *)
Definition vren_shift_point (m : sort) : vren :=
  fun m' => if eq_dec m m' then rshift else rid.

(** Lift a vector of renamings through a binder for sort [m]. *)
Definition vrup (m : sort) (rv : vren) : vren :=
  fun m' => if eq_dec m m' then rup (rv m') else (rv m').

(** Apply a vector of renamings to an expression. *)
Equations rename {k} (rv : vren) (t : expr k) : expr k :=
rename rv (@E_var m i) := E_var (rv m i) ;
rename rv (E_ctor c al) := E_ctor c (rename rv al) ;
rename rv E_al_nil := E_al_nil ;
rename rv (E_al_cons a al) := E_al_cons (rename rv a) (rename rv al) ;
rename rv (E_abase b x) := E_abase b x ;
rename rv (E_aterm t) := E_aterm (rename rv t) ;
rename rv (E_abind m a) := E_abind m (rename (vrup m rv) a).

(** Compose of two vectors of renamings. *)
Definition vrcomp (r1 r2 : vren) : vren :=
  fun m => rcomp (r1 m) (r2 m).

(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A single substitution which yields terms of sort [m]. *)
Definition subst m := nat -> term  m.

(** A vector of substitutions. *)
Definition vsubst := forall m, subst m.

(** The identity substitution. *)
Definition sid {m} : subst m := fun i => E_var i.

(** A vector of identity substitutions. *)
Definition vsid : vsubst := fun _ => sid.

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
Definition vsup (m : sort) (svec : vsubst) : vsubst :=
  let r := vren_shift_point m in 
  fun m' => 
    if eq_dec m m' 
    then scons (E_var 0) (svrcomp (svec m') r) 
    else svrcomp (svec m') r.

(** Apply a vector of substitutions to an expression. *)
Equations substitute {k} (svec : vsubst) (t : expr k) : expr k :=
substitute svec (@E_var m i) := svec m i ;
substitute svec (E_ctor c al) := E_ctor c (substitute svec al) ;
substitute svec E_al_nil := E_al_nil ;
substitute svec (E_al_cons a al) := E_al_cons (substitute svec a) (substitute svec al) ;
substitute svec (E_abase b x) := E_abase b x ;
substitute svec (E_aterm t) := E_aterm (substitute svec t) ;
substitute svec (E_abind m a) := E_abind m (substitute (vsup m svec) a).

(** Compose of a substitution with a vector of substitutions. *)
Definition svscomp {m} (s : subst m) (svec : vsubst) : subst m :=
  fun i => substitute svec (s i).

(** Compose of two vectors of substitutions. *)
Definition vscomp (s1 s2 : vsubst) : vsubst :=
  fun m => svscomp (s1 m) s2.

(** Compose of a vector of renamings with a vector of substitutions. *)
Definition vrvscomp (r : vren) (s : vsubst) : vsubst := 
  fun m => rscomp (r m) (s m).  

(** Compose of a vector of substitutions with a vector of renamings. *)
Definition vsvrcomp (s : vsubst) (r : vren) : vsubst := 
  fun m => svrcomp (s m) r.  
  
(*********************************************************************************)
(** *** Setoid Rewrite lemmas. *)
(*********************************************************************************)

#[export] Instance up_vren_proper : Proper (eq ==> eq2 ==> eq2) vrup.
Proof.
intros m ? <- rv rv' Hrv m' i. unfold vrup.
destruct (eq_dec m m').
- apply rup_proper. apply Hrv.
- now rewrite Hrv. 
Qed.

#[export] Instance rename_proper k : Proper (eq2 ==> eq ==> eq) (@rename k).
Proof.
intros rv rv' Hr t _ <-. induction t in rv, rv', Hr |- * ; simp rename.
all: try solve [ f_equal ; auto ].
- now rewrite Hr. 
- f_equal. apply IHt. now rewrite Hr.
Qed.

#[export] Instance vrcomp_proper : Proper (eq2 ==> eq2 ==> eq2) vrcomp.
Proof.
intros r1 r1' H1 r2 r2' H2 m. unfold vrcomp. now rewrite (H1 m), (H2 m).
Qed.

#[export] Instance svrcomp_proper m : Proper (eq1 ==> eq2 ==> eq1) (@svrcomp m).
Proof. intros s s' Hs r r' Hr i. unfold svrcomp. now rewrite Hr, Hs. Qed.

#[export] Instance rscomp_proper m : Proper (eq1 ==> eq1 ==> eq1) (@rscomp m).
Proof. intros r r' Hr s s' Hs i. unfold rscomp. now rewrite Hr, Hs. Qed.

#[export] Instance scons_proper m : Proper (eq ==> eq1 ==> eq1) (@scons m).
Proof. intros t ? <- s s' Hs i. unfold scons. now destruct i. Qed.

#[export] Instance vsup_proper : Proper (eq ==> eq2 ==> eq2) vsup.
Proof.
intros m ? <- svec svec' Hs m'. unfold vsup. destruct (eq_dec m m').
- rewrite <-e. apply scons_proper ; [reflexivity|]. apply svrcomp_proper. 
  + apply Hs.
  + reflexivity.
- apply svrcomp_proper.
  + apply Hs.
  + reflexivity.
Qed.  

#[export] Instance substitute_proper k : Proper (eq2 ==> eq ==> eq) (@substitute k).
Proof.
intros svec svec' Hs t ? <-. induction t in svec, svec', Hs |- * ; simp substitute.
all: try solve [ f_equal ; auto ].
f_equal. apply IHt. now rewrite Hs.
Qed.

#[export] Instance svscomp_proper m : Proper (eq1 ==> eq2 ==> eq1) (@svscomp m).
Proof. intros s s' Hs svec svec' Hsvec i. unfold svscomp. now rewrite Hs, Hsvec. Qed.

#[export] Instance vscomp_proper : Proper (eq2 ==> eq2 ==> eq2) vscomp.
Proof.
intros s1 s1' H1 s2 s2' H2 m. unfold vscomp. now rewrite (H1 m), H2.
Qed.

#[export] Instance vrvscomp_proper : Proper (eq2 ==> eq2 ==> eq2) vrvscomp.
Proof. intros r r' Hr s s' Hs m. unfold vrvscomp. now rewrite (Hr m), (Hs m). Qed.

#[export] Instance vsvrcomp_proper : Proper (eq2 ==> eq2 ==> eq2) vsvrcomp.
Proof. intros s s' Hs r r' Hr m. unfold vsvrcomp. now rewrite Hr, (Hs m). Qed.

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
  
Lemma vrup_id {m} : vrup m vrid =₂ vrid.
Proof. 
intros m' i. unfold vrup. destruct (eq_dec m m').
- subst. now rewrite rup_id.
- reflexivity.
Qed.

Lemma comp_vrup_vrup {m} r1 r2 : 
  vrcomp (vrup m r1) (vrup m r2) =₂ vrup m (vrcomp r1 r2).
Proof.
intros m' i. unfold vrcomp, vrup. destruct (eq_dec m m').
- subst. now rewrite comp_rup_rup.
- reflexivity.
Qed. 

Lemma rename_id {k} (t : expr k) : rename vrid t = t.
Proof.
induction t ; simp rename.
all: try solve [ f_equal ; auto ].
now rewrite vrup_id, IHt.
Qed.

Lemma vsup_id {m} : vsup m vsid =₂ vsid.
Proof. 
intros m' i. unfold vsup, vsid. destruct (eq_dec m m') ; subst ; cbn.
- destruct i ; cbn ; [reflexivity|]. unfold vren_shift_point. 
  now rewrite eq_dec_refl.
- unfold vren_shift_point. destruct (eq_dec m m').
  + now apply n in e. 
  + reflexivity.
Qed.

Lemma substitute_id {k} (t : expr k) : substitute vsid t = t.
Proof.
induction t ; simp substitute in * ; f_equal ; auto.
now rewrite vsup_id. 
Qed.

Lemma rename_rename {k} (t : expr k) (r1 r2 : vren) : 
  rename r2 (rename r1 t) = rename (vrcomp r1 r2) t.
Proof.
induction t in r1, r2 |- * ; simp rename in * ; f_equal ; auto.
now rewrite IHt, comp_vrup_vrup.
Qed.

Lemma comp_vrup_vsup {m} r s : 
  vrvscomp (vrup m r) (vsup m s) =₂ vsup m (vrvscomp r s).
Proof.
intros m'. unfold vrvscomp, vrup, vsup. destruct (eq_dec m m').
- subst. intros i. unfold rscomp. destruct i ; reflexivity.
- intros i. reflexivity.
Qed. 

Lemma substitute_rename {k} (t : expr k) (r : vren) (s : vsubst) : 
  substitute s (rename r t) = substitute (vrvscomp r s) t.
Proof.
induction t in r, s |- * ; simp rename substitute in * ; f_equal ; auto.
now rewrite IHt, comp_vrup_vsup.
Qed.

Lemma comp_vsup_vrup {m} s r :
  vsvrcomp (vsup m s) (vrup m r) =₂ vsup m (vsvrcomp s r).
Proof.
intros m'. unfold vsvrcomp, vsup, vrup, svrcomp. destruct (eq_dec m m').
- subst. intros i. destruct i ; cbn.
  + rewrite eq_dec_refl. reflexivity.
  + rewrite !rename_rename. apply rename_proper ; [|reflexivity].
    clear s i. intros m i. unfold vrcomp, vren_shift_point.
    destruct (eq_dec m' m) ; subst ; reflexivity.
- intros i. rewrite !rename_rename. apply rename_proper ; [|reflexivity].
  clear s i. intros m'' i. unfold vrcomp, vren_shift_point.
  destruct (eq_dec m m'') ; subst ; reflexivity.
Qed.

Lemma rename_substitute {k} (t : expr k) (s : vsubst) (r : vren) : 
  rename r (substitute s t) = substitute (vsvrcomp s r) t.
Proof.
induction t in s, r |- * ; simp rename substitute in * ; f_equal ; auto.
now rewrite IHt, comp_vsup_vrup.
Qed.

Lemma comp_vsup_vsup {m} s1 s2 :
  vscomp (vsup m s1) (vsup m s2) =₂ vsup m (vscomp s1 s2).
Proof.
intros m' i. unfold vscomp, vsup, svscomp, svrcomp. destruct (eq_dec m m').
- subst. destruct i.
  + cbn. rewrite eq_dec_refl. reflexivity.
  + cbn. rewrite substitute_rename, rename_substitute.
    apply substitute_proper ; [|reflexivity]. clear s1 i.
    intros m i. unfold vrvscomp, vren_shift_point, vsvrcomp, svrcomp, rscomp.
    destruct (eq_dec m' m) ; subst ; reflexivity.
- rewrite substitute_rename, rename_substitute. 
  apply substitute_proper ; [|reflexivity]. clear s1 i.
  intros m'' i. unfold vrvscomp, vren_shift_point. 
  destruct (eq_dec m m'') ; subst ; reflexivity.
Qed.

Lemma substitute_substitute {k} (t : expr k) (s1 s2 : vsubst) : 
  substitute s2 (substitute s1 t) = substitute (vscomp s1 s2) t.
Proof.
induction t in s1, s2 |- * ; simp substitute ; f_equal ; auto.
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