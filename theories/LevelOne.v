From Prototype Require Import Prelude Sig.

(** This file defines a generic term grammar with _admissible_ renamings 
    and substitutions, i.e. renamings are functions [nat -> nat] 
    and substitutions are functions [nat -> term].
    
    We prove the main properties of substitution and renaming. *)

Module Make (S : Sig).

(** Add some power to [auto] and variants. *)
#[local] Hint Extern 4 => f_equal : core.

(*********************************************************************************)
(** *** Terms. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Terms over an abstract signature. 
    Terms are indexed by a kind. *)
Inductive expr : kind -> Type :=
| (** Term variable. *)
  E_var : nat -> term
| (** Non-variable expr constructor, applied to a list of arguments. *)
  E_ctor : forall c, args (ctor_type S.t c) -> term
| (** Empty argument list. *)
  E_al_nil : args []
| (** Non-empty argument list. *)
  E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)
| (** Base argument (e.g. bool or string). *)
  E_abase : forall b, eval_base S.t b -> arg (AT_base b)
| (** Term argument. *)
  E_aterm : term -> arg AT_term
| (** Binder argument. *)
  E_abind {ty} : arg ty -> arg (AT_bind ty)
where "'term'" := (expr Kt)
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

Derive Signature for expr.

(** Size of an expression. This is used in the plugin to prove a custom 
    induction principle for level one terms instantiated to a specific
    signature. We deliberately use a fixpoint here so that [simpl] works. *)
Fixpoint esize {k} (t : expr k) : nat :=
  match t with 
  | E_var _ => 0
  | E_ctor c al => S (esize al)
  | E_al_nil => 0
  | E_al_cons a al => S (esize a + esize al)
  | E_abase _ _ => 0
  | E_aterm t => S (esize t)
  | E_abind a => S (esize a)
  end.

(** In order to avoid using [depelim] in the plugin, we prove simple inversion lemmas
    which we then use in the plugin when generating the custom 
    induction principle on level one terms. *)

Section InvLemmas.
  Lemma inv_Kt (P : term -> Prop) (t : term) :
    (forall i, P (E_var i)) -> (forall c al, P (E_ctor c al)) -> P t.
  Proof. depelim t ; eauto. Qed.
  
  Lemma inv_Kal_nil (P : args [] -> Prop) (al : args []) : P E_al_nil -> P al.
  Proof. depelim al ; eauto. Qed.

  Lemma inv_Kal_cons {ty tys} (P : args (ty :: tys) -> Prop) (al : args (ty :: tys)) : 
    (forall a al', P (E_al_cons a al')) -> P al.
  Proof. depelim al ; eauto. Qed.
  
  Lemma inv_Ka_term (P : arg AT_term -> Prop) (a : arg AT_term) : 
    (forall t, P (E_aterm t)) -> P a.
  Proof. depelim a ; eauto. Qed.
  
  Lemma inv_Ka_base {b} (P : arg (AT_base b) -> Prop) (a : arg (AT_base b)) :
    (forall x, P (E_abase b x)) -> P a.
  Proof. depelim a ; eauto. Qed.
  
  Lemma inv_Ka_bind {ty} (P : arg (AT_bind ty) -> Prop) (a : arg (AT_bind ty)) :
    (forall a', P (E_abind a')) -> P a.
  Proof. depelim a ; eauto. Qed.
End InvLemmas.

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)
 
(** Rename a term. *)
Equations rename {k} (r : ren) (t : expr k) : expr k :=
rename r (E_var i) := E_var (r i) ;
rename r (E_ctor c al) := E_ctor c (rename r al) ;
rename r E_al_nil := E_al_nil ;
rename r (E_al_cons a al) := E_al_cons (rename r a) (rename r al) ;
rename r (E_abase b x) := E_abase b x ;
rename r (E_aterm t) := E_aterm (rename r t) ;
rename r (E_abind a) := E_abind (rename (up_ren r) a).

(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A substitution on terms is a function [nat -> term] which is applied 
    to all free variables. *)
Definition subst := nat -> term.

(** The identity substitution. *)
Definition sid : subst := fun i => E_var i.

(** [sshift] shifts indices by one. *)
Definition sshift : subst := 
  fun i => E_var (S i).

(** Cons a expr with a substitution. *)
Equations scons (t : term) (s : subst) : subst :=
scons t s 0 := t ;
scons t s (S i) := s i.

(** Left to right composition of a substitution with a renaming. *)
Definition srcomp (s : subst) (r : ren) := 
  fun i => rename r (s i).

(** Left to right composition of a renaming with a substitution. *)
Definition rscomp (r : ren) (s : subst) := 
  fun i => s (r i).

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  scons (E_var 0) (srcomp s rshift).

(** Apply a substitution to a expr. *)
Equations substitute {k} (s : subst) (t : expr k) : expr k :=
substitute s (E_var i) := s i ;
substitute s (E_ctor c al) := E_ctor c (substitute s al) ;
substitute s E_al_nil := E_al_nil ;
substitute s (E_al_cons a al) := E_al_cons (substitute s a) (substitute s al) ;
substitute s (E_abase b x) := E_abase b x ;
substitute s (E_aterm t) := E_aterm (substitute s t) ;
substitute s (E_abind a) := E_abind (substitute (up_subst s) a).

(** Left to right composition of substitutions. *)
Definition scomp (s1 s2 : subst) : subst :=
  fun i => substitute s2 (s1 i).

(*********************************************************************************)
(** *** Setoid Rewrite Support. *)
(*********************************************************************************)

#[global] Instance up_ren_proper : Proper (point_eq ==> point_eq) up_ren.
Proof. 
intros r1 r2 Hr i. destruct i ; cbv [rcons up_ren rcomp].
- reflexivity.
- now rewrite Hr.
Qed. 

#[global] Instance rcons_proper : Proper (eq ==> point_eq ==> point_eq) rcons.
Proof. intros i1 i2 it s1 s2 Hs i. destruct i ; simp rcons. now rewrite Hs. Qed.

#[global] Instance rcomp_proper : Proper (point_eq ==> point_eq ==> point_eq) rcomp.
Proof. 
intros s1 s2 Hs r1 r2 Hr i. destruct i ; cbv [rcomp].
- now rewrite Hs, Hr.
- now rewrite Hs, Hr.
Qed.

#[global] Instance rename_proper k :
  Proper (point_eq ==> eq ==> eq) (@rename k).
Proof.
intros r1 r2 Hr t _ <-. funelim (rename _ _) ; simp rename in * ; auto.
f_equal. apply H. now rewrite Hr.
Qed.

#[global] Instance rscomp_proper : Proper (point_eq ==> point_eq ==> point_eq) rscomp.
Proof. intros r1 r2 Hr s1 s2 Hs i. cbv [rscomp]. now rewrite Hs, Hr. Qed.

#[global] Instance srcomp_proper : Proper (point_eq ==> point_eq ==> point_eq) srcomp.
Proof. intros s1 s2 Hs r1 r2 Hr i. cbv [srcomp]. now rewrite Hs, Hr. Qed.

#[global] Instance scons_proper : Proper (eq ==> point_eq ==> point_eq) scons.
Proof. 
intros t1 t2 Ht s1 s2 Hs i. 
destruct i ; simp scons. now rewrite Hs. 
Qed.

#[global] Instance up_subst_proper : Proper (point_eq ==> point_eq) up_subst.
Proof. intros s1 s2 Hs. cbv [up_subst]. now rewrite Hs. Qed.

#[global] Instance substitute_proper k : 
  Proper (point_eq ==> eq ==> eq) (@substitute k).
Proof. 
intros s1 s2 Hs t ? <-. funelim (substitute _ _) ; simp substitute in * ; auto.
f_equal. apply H. now rewrite Hs.
Qed. 

#[global] Instance scomp_proper : Proper (point_eq ==> point_eq ==> point_eq) scomp.
Proof. intros s1 s2 Hs r1 r2 Hr i. cbv [scomp]. now rewrite Hs, Hr. Qed.

(*********************************************************************************)
(** *** Properties of renaming and substitution. *)
(*********************************************************************************)

Lemma rid_rcons : rcons 0 rshift =₁ rid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma sid_scons : scons (E_var 0) sshift =₁ sid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma rcomp_rcons_distrib i (r1 r2 : ren) :
  rcomp (rcons i r1) r2 =₁ rcons (r2 i) (rcomp r1 r2).
Proof. intros [|i'] ; reflexivity. Qed.

Lemma scomp_scons_distrib (t : term) (s1 s2 : subst) :
  scomp (scons t s1) s2 =₁ scons (substitute s2 t) (scomp s1 s2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma rshift_rcons i (r : ren) : rcomp rshift (rcons i r) =₁ r.
Proof. reflexivity. Qed.
    
Lemma sshift_scons (t : term) (s : subst) : scomp sshift (scons t s) =₁ s.
Proof. reflexivity. Qed.

Lemma rcomp_rid_l (r : ren) : rcomp rid r =₁ r.
Proof. reflexivity. Qed.

Lemma rcomp_rid_r (r : ren) : rcomp r rid =₁ r.
Proof. reflexivity. Qed.

Lemma rcomp_assoc (r1 r2 r3 : ren) : 
  rcomp (rcomp r1 r2) r3 =₁ rcomp r1 (rcomp r2 r3).
Proof. reflexivity. Qed.

Lemma up_ren_rid : up_ren rid =₁ rid.
Proof. intros [|] ; reflexivity. Qed.

Lemma up_ren_comp (r1 r2 : ren) : 
  rcomp (up_ren r1) (up_ren r2) =₁ up_ren (rcomp r1 r2).
Proof. intros [|i] ; reflexivity. Qed.

Lemma ren_rid {k} (t : expr k) : rename rid t = t.
Proof. induction t ; simp rename ; triv. now rewrite up_ren_rid, IHt. Qed.

Lemma ren_ren {k} (t : expr k) (r1 r2 : ren) : 
  rename r2 (rename r1 t) = rename (rcomp r1 r2) t.
Proof.
funelim (rename _ t) ; simp rename in * ; auto.
now rewrite H, up_ren_comp.
Qed.

Lemma ren_subst {k} (t : expr k) (s : subst) (r : ren) : 
  rename r (substitute s t) = substitute (srcomp s r) t.
Proof.
funelim (substitute _ t) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; auto. cbv [up_subst scons srcomp].
rewrite ren_ren, ren_ren. apply rename_proper ; auto.
reflexivity.
Qed.

Lemma subst_ren {k} (t : expr k) (r : ren) (s : subst) : 
  substitute s (rename r t) = substitute (rscomp r s) t.
Proof.
funelim (rename r t) ; simp rename substitute in * ; auto.
f_equal. rewrite H. apply substitute_proper ; auto.
intros [|i] ; reflexivity.
Qed.

Lemma up_subst_comp (s1 s2 : subst) : 
  scomp (up_subst s1) (up_subst s2) =₁ up_subst (scomp s1 s2).
Proof. 
intros [|i] ; auto. cbv [up_subst scomp]. simp scons. cbv [srcomp].
rewrite ren_subst, subst_ren. now apply substitute_proper.
Qed.

Lemma subst_subst {k} (t : expr k) (s1 s2 : subst) : 
  substitute s2 (substitute s1 t) = substitute (scomp s1 s2) t.
Proof.
funelim (substitute _ t) ; simp substitute ; auto.
rewrite H. now rewrite up_subst_comp.
Qed.

Lemma up_subst_sid : up_subst sid =₁ sid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma subst_sid {k} (t : expr k) : substitute sid t = t.
Proof.
induction t ; simp substitute in * ; auto.
rewrite up_subst_sid. auto.
Qed.

Lemma scomp_sid_l (s : subst) : scomp sid s =₁ s.
Proof. reflexivity. Qed.

Lemma scomp_sid_r (s : subst) : scomp s sid =₁ s.
Proof. intros i. cbv [scomp]. now rewrite subst_sid. Qed.

Lemma scomp_assoc (s1 s2 s3 : subst) : 
  scomp (scomp s1 s2) s3 =₁ scomp s1 (scomp s2 s3).
Proof. intros i. cbv [scomp]. now rewrite subst_subst. Qed.

Lemma ren_is_subst {k} (t : expr k) (r : ren) : 
  rename r t = substitute (rscomp r E_var) t.
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
Qed.

End Make.