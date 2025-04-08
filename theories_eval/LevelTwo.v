From Prototype Require Import Prelude Sig LevelOne.

Module Make (S : Sig).
Module O := LevelOne.Make (S).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Expressions (terms and explicit substitutions). *)
(*********************************************************************************)

(** Kind of a term, argument, or argument list. *)
Inductive mono_kind :=
| (** Term. *)
  Kt : mono_kind
| (** Constructor argument. *)
  Ka : arg_ty -> mono_kind
| (** List of constructor arguments. *)
  Kal : list arg_ty -> mono_kind.
Derive NoConfusion for mono_kind.

(** Kind of a renaming or substitution. *)
Inductive bi_kind :=
| (** Renaming *) 
  Kr : bi_kind
| (** Substitution. *)
  Ks : bi_kind.
Derive NoConfusion for bi_kind.

(** Expressions are indexed by kinds. *)
Inductive kind : Type := 
| (** Term-like. *)
  Km : mono_kind -> kind
| (** Substitution-like. *)
  Kb : bi_kind -> kind.  
Derive NoConfusion for kind.

Definition denote_type (k : kind) : Type :=
  match k with 
  | Km k' => 
    (* Since [denote_type] is used in types a lot, it is important that it computes
       as much as possible. We match on [k'] rather late so that [denote_type (Km _)]
       is not stuck and computes to [O.expr _]. *)
    O.expr (match k' with Kt => O.Kt | Ka ty => O.Ka ty | Kal tys => O.Kal tys end)
  | Kb Kr => O.ren
  | Kb Ks => O.subst
  end.

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).
Reserved Notation "'ren'" (at level 0).
Reserved Notation "'subst'" (at level 0).

(** Expressions over an abstract signature. 
    Expressions are indexed by a kind: this is to avoid writing a mutual inductives,
    which would be hard to manipulate. *)
Inductive expr : kind -> Type :=

| (** Variable term constructor (de Bruijn index). *)
  E_tvar : nat -> term
| (** Non-variable term constructor, applied to a list of arguments. *)
  E_tctor : forall c, args (ctor_type S.t c) -> term

| (** Empty argument list. *)
  E_al_nil : args []
| (** Non-empty argument list. *)
  E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

| (** Base argument (e.g. bool or string). *)
  E_abase : forall b, denote_base S.t b -> arg (AT_base b)
| (** Term argument. *)
  E_aterm : term -> arg AT_term
| (** Binder argument. *)
  E_abind {ty} : arg ty -> arg (AT_bind ty)

| (** Shift renaming. *)
  E_rshift : nat -> ren
| (** Renaming expansion. *)
  E_rcons : nat -> ren -> ren
| (** Renaming composition. *)
  E_rcomp : ren -> ren -> ren

| (** Shift substitution. *)
  E_sshift : nat -> subst
| (** Substitution expansion. *)
  E_scons : term -> subst -> subst
| (** Substitution composition. *)
  E_scomp : subst -> subst -> subst
| (** View a renaming as a substitution. *)
  E_sren : ren -> subst

| (** Instantiate a term/argument/argument-list with a renaming. *)
  E_rinst {k} : expr (Km k) -> ren -> expr (Km k)
| (** Instantiate a term/argument/argument-list with a substitution. *)
  E_sinst {k} : expr (Km k) -> subst -> expr (Km k)
| (** Metavariable (of any kind). *)
  E_mvar {k} : denote_type k -> expr k

where "'term'" := (expr (Km Kt))
  and "'arg' ty" := (expr (Km (Ka ty)))
  and "'args' tys" := (expr (Km (Kal tys)))
  and "'ren'" := (expr (Kb Kr))
  and "'subst'" := (expr (Kb Ks)).

Derive Signature NoConfusion for expr.

(** Notations for common expressions. *)

Notation "'↑ᵣ' k" := (E_rshift k) (at level 0, k at level 0).
Notation "i '.ᵣ' r" := (E_rcons i r) (at level 60, right associativity).
Notation "r1 '>>ᵣ' r2" := (E_rcomp r1 r2) (at level 50, left associativity).

Notation "'↑ₛ' k" := (E_sshift k) (at level 0, k at level 0).
Notation "t '.ₛ' s" := (E_scons t s) (at level 60, right associativity).
Notation "s1 '>>ₛ' s2" := (E_scomp s1 s2) (at level 50, left associativity).

Notation "t '[ᵣ' s ']'" := (E_rinst t s) (at level 15, s at level 0, no associativity).
Notation "t '[ₛ' s ']'" := (E_sinst t s) (at level 15, s at level 0, no associativity).

(** The identity renaming. *)
Definition rid : ren := E_rshift 0.

(** The identity substitution. *)
Definition sid : subst := E_sshift 0.

(** Lift a renaming through a binder. *)
Definition up_ren (r : ren) : ren :=
  0 .ᵣ r >>ᵣ ↑ᵣ1.

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  E_tvar 0 .ₛ s >>ₛ ↑ₛ1.

(*********************************************************************************)
(** *** Denotation. *)
(*********************************************************************************)

(** Mapping from level two expressions to level one expressions and substitutions. *)
Equations denote {k} (t : expr k) : denote_type k by struct t :=

denote (E_tvar i) := O.E_var i ;
denote (E_tctor c al) := O.E_ctor c (denote al) ;

denote E_al_nil := O.E_al_nil ;
denote (E_al_cons a al) := O.E_al_cons (denote a) (denote al) ;

denote (E_abase b x) := O.E_abase b x ;
denote (E_aterm t) := O.E_aterm (denote t) ;
denote (E_abind a) := O.E_abind (denote a) ;

denote (E_rshift k) := O.rshift k ;
denote (E_rcons i r) := O.rcons i (denote r) ;
denote (E_rcomp r1 r2) := O.rcomp (denote r1) (denote r2) ;

denote (E_sshift k) := O.sshift k ;
denote (E_scons t s) := O.scons (denote t) (denote s) ;
denote (E_scomp s1 s2) := O.scomp (denote s1) (denote s2) ;
denote (E_sren r) := fun i => O.E_var (denote r i) ;

denote (@E_sinst Kt t s) := O.substitute (denote t) (denote s) ;
denote (@E_sinst (Ka _) t s) := O.substitute (denote t) (denote s) ;
denote (@E_sinst (Kal _) t s) := O.substitute (denote t) (denote s) ;
denote (@E_rinst Kt t s) := O.rename (denote t) (denote s) ;
denote (@E_rinst (Ka _) t s) := O.rename (denote t) (denote s) ;
denote (@E_rinst (Kal _) t s) := O.rename (denote t) (denote s) ;
denote (E_mvar x) := x.

(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

Ltac2 rec reify_term (t : constr) : constr :=
  lazy_match! t with 
  | O.E_var ?i => constr:(E_tvar $i)
  | O.E_ctor ?c ?al => 
    let al := reify_term al in
    constr:(E_tctor $c $al)
  | O.E_al_nil => constr:(E_al_nil)
  | O.E_al_cons ?a ?al => 
    let a := reify_term a in
    let al := reify_term al in
    constr:(E_al_cons $a $al)
  | O.E_abase ?b ?x => constr:(E_abase $b $x)
  | O.E_aterm ?t => 
    let t := reify_term t in
    constr:(E_aterm $t)
  | O.E_abind ?a =>
    let a := reify_term a in
    constr:(E_abind $a)
  | O.rename ?t ?r =>
    let t := reify_term t in
    let r := reify_ren r in
    constr:(E_rinst $t $r)
  | O.substitute ?t ?s =>
    let t := reify_term t in
    let s := reify_subst s in
    constr:(E_sinst $t $s)
  | _ => constr:(@E_mvar (Km Kt) $t)
  end
with reify_subst (s : constr) : constr :=
  lazy_match! s with 
  | O.sid => constr:(sid)
  | O.sshift ?k => constr:(E_sshift $k)
  | O.scons ?t ?s =>
    let t := reify_term t in 
    let s := reify_subst s in 
    constr:(E_scons $t $s)
  | O.scomp ?s1 ?s2 =>
    let s1 := reify_subst s1 in 
    let s2 := reify_subst s2 in 
    constr:(E_scomp $s1 $s2)
  | fun i => O.rename (?s i) ?r =>
    let s := reify_subst s in 
    let r := reify_ren r in
    constr:(E_scomp $s (E_sren $r))
  | ?s => constr:(@E_mvar (Kb Ks) $s)
  end
with reify_ren (r : constr) : constr := 
  lazy_match! r with 
  | O.rid => constr:(rid)
  | O.rshift ?k => constr:(E_rshift $k)
  | O.rcons ?i ?r => 
    let r := reify_ren r in 
    constr:(E_rcons $i $r)
  | ?r => constr:(@E_mvar (Kb Kr) $r)
  end.

(*********************************************************************************)
(** *** Normal form expressions. *)
(*********************************************************************************)

Reserved Notation "'nf_term'" (at level 0).
Reserved Notation "'nf_arg' ty" (at level 0, ty at level 0).
Reserved Notation "'nf_args' tys" (at level 0, tys at level 0).
Reserved Notation "'nf_ren'" (at level 0).
Reserved Notation "'nf_subst'" (at level 0).

(** Normal form expressions. *)
Inductive nf_expr : kind -> Type :=

| N_tvar : nat -> nf_term
| N_tctor : forall c, nf_args (ctor_type S.t c) -> nf_term
| N_al_nil : nf_args []
| N_al_cons {ty tys} : nf_arg ty -> nf_args tys -> nf_args (ty :: tys)
| N_abase : forall b, denote_base S.t b -> nf_arg (AT_base b)
| N_aterm : nf_term -> nf_arg AT_term
| N_abind {ty} : nf_arg ty -> nf_arg (AT_bind ty)

| N_rshift : nat -> nf_ren
| N_rcons : nat -> nf_ren -> nf_ren
(** Composition of renamings, where the left hand side is a 
    (possibly lifted) metavariable. *)
|  N_rcomp : nat -> denote_type (Kb Kr) -> nf_ren -> nf_ren

| N_sshift : nat -> nf_subst
| N_scons : nf_term -> nf_subst -> nf_subst
(** Composition of substitutions, where the left hand side is a 
    (possibly lifted) metavariable. *)
| N_scomp : nat -> denote_type (Kb Ks) -> nf_subst -> nf_subst
| N_sren : nf_ren -> nf_subst

(** Instantiation with a renaming/substitution, where the left hand side 
    is a metavariable. *)  
| N_rinst_l {k} : denote_type (Km k) -> nf_ren -> nf_expr (Km k)
| N_sinst_l {k} : denote_type (Km k) -> nf_subst -> nf_expr (Km k)
(** Instantiation with a renaming/substitution, where the right hand side 
    is a metavariable (possibly composed with some other renaming/substitution),
    and the left hand side is a de Bruijn index. *)
| N_rinst_r : nat -> denote_type (Kb Kr) -> nf_ren -> nf_term
| N_sinst_r : nat -> denote_type (Kb Ks) -> nf_subst -> nf_term

where "'nf_term'" := (nf_expr (Km Kt))
  and "'nf_arg' ty" := (nf_expr (Km (Ka ty)))
  and "'nf_args' tys" := (nf_expr (Km (Kal tys)))
  and "'nf_ren'" := (nf_expr (Kb Kr))
  and "'nf_subst'" := (nf_expr (Kb Ks)).

(** Denote a normal form expression. *)
Equations denote_nf {k} : nf_expr k -> denote_type k :=

denote_nf (N_tvar i) := O.E_var i ;
denote_nf (N_tctor c al) := O.E_ctor c (denote_nf al) ;
denote_nf N_al_nil := O.E_al_nil ;
denote_nf (N_al_cons a al) := O.E_al_cons (denote_nf a) (denote_nf al) ;
denote_nf (N_abase b x) := O.E_abase b x ;
denote_nf (N_aterm t) := O.E_aterm (denote_nf t) ;
denote_nf (N_abind a) := O.E_abind (denote_nf a) ;

denote_nf (N_rshift k) := O.rshift k ;
denote_nf (N_rcons i r) := O.rcons i (denote_nf r) ;
denote_nf (N_rcomp k xr r) := O.rcomp (O.rcomp (O.rshift k) xr) (denote_nf r) ;

denote_nf (N_sshift k) := O.sshift k ;
denote_nf (N_scons t s) := O.scons (denote_nf t) (denote_nf s) ;
denote_nf (N_scomp k xs s) := O.scomp (O.scomp (O.sshift k) xs) (denote_nf s) ;
denote_nf (N_sren r) := fun i => O.E_var (denote_nf r i) ;

denote_nf (@N_rinst_l Kt xt r) := O.rename xt (denote_nf r) ;
denote_nf (@N_rinst_l (Ka _) xt r) := O.rename xt (denote_nf r) ;
denote_nf (@N_rinst_l (Kal _) xt r) := O.rename xt (denote_nf r) ;

denote_nf (@N_sinst_l Kt xt s) := O.substitute xt (denote_nf s) ;
denote_nf (@N_sinst_l (Ka _) xt s) := O.substitute xt (denote_nf s) ;
denote_nf (@N_sinst_l (Kal _) xt s) := O.substitute xt (denote_nf s) ;

denote_nf (N_rinst_r i xr r) := O.rename (O.E_var i) (O.rcomp xr (denote_nf r)) ;
denote_nf (N_sinst_r i xs s) := O.substitute (O.E_var i) (O.scomp xs (denote_nf s)).

(*********************************************************************************)
(** *** Normalization. *)
(*********************************************************************************)

(** Tail of a normal form renaming. *)
Equations rtail : nf_ren -> nf_ren := 
rtail (N_rshift k) := N_rshift (S k) ;
rtail (N_rcons _ r) := r ;
rtail (N_rcomp k xr r) := N_rcomp (S k) xr r.

Lemma rtail_sound r : denote_nf (rtail r) =₁ O.rcomp (O.rshift 1) (denote_nf r).
Proof. 
funelim (rtail r) ; simp rtail denote_nf.
- now rewrite O.rshift_succ_l.
- now rewrite O.rshift_rcons.
- repeat rewrite <-O.rcomp_assoc. now rewrite O.rshift_succ_l.
Qed.     

(** Drop the first [k] elements in a normal form renaming. *)
Equations rdrop : nat -> nf_ren -> nf_ren :=
rdrop 0 r := r ;
rdrop (S k) r := rtail (rdrop k r).

Lemma rdrop_sound k r : denote_nf (rdrop k r) =₁ O.rcomp (O.rshift k) (denote_nf r).
Proof.
funelim (rdrop k r) ; simp denote_nf.
- now rewrite O.rcomp_rid_l.
- rewrite rtail_sound, H. now rewrite <-O.rcomp_assoc, O.rshift_succ_l.
Qed.  

(** Apply a normal form renaming to a de Bruijn index. *)
Equations rapply : nf_ren -> nat -> nat :=
rapply (N_rshift k) i := k + i ;
rapply (N_rcons i _) 0 := i ;
rapply (N_rcons _ r) (S i) := rapply r i ;
rapply (N_rcomp k xr r) i := rapply r (xr (k + i)).

Lemma rapply_sound r i : rapply r i = denote_nf r i.
Proof. funelim (rapply r i) ; simp denote_nf ; solve [ auto ]. Qed.
    
(** Compose two normal form renamings. *)
Equations rcomp : nf_ren -> nf_ren -> nf_ren :=
rcomp (N_rshift k) r := rdrop k r ;
rcomp (N_rcons i r1) r2 := N_rcons (rapply r2 i) (rcomp r1 r2) ;
rcomp (N_rcomp k xr r1) r2 := N_rcomp k xr (rcomp r1 r2).

Lemma rcomp_sound r1 r2 : 
  denote_nf (rcomp r1 r2) =₁ O.rcomp (denote_nf r1) (denote_nf r2).
Proof.
funelim (rcomp r1 r2) ; simp denote_nf.
- now rewrite rdrop_sound.
- now rewrite rapply_sound, O.rcomp_rcons_distrib, H.
- rewrite H. now repeat rewrite O.rcomp_assoc.
Qed.

(** Lift a normal form renaming through a binder. *)
Equations rup : nf_ren -> nf_ren :=
rup r := N_rcons 0 (rcomp r (N_rshift 1)).

Lemma rup_sound r : denote_nf (rup r) =₁ O.up_ren (denote_nf r).
Proof. simp rup denote_nf. unfold O.up_ren. now rewrite rcomp_sound. Qed.

(** Instantiate a normal form term with a normal form renaming. *)
Equations rinst {k} : nf_expr (Km k) -> nf_ren -> nf_expr (Km k) :=
rinst (N_tvar i) r := N_tvar (rapply r i) ;
rinst (N_tctor c al) r := N_tctor c (rinst al r) ;
rinst N_al_nil _ := N_al_nil ;
rinst (N_al_cons a al) r := N_al_cons (rinst a r) (rinst al r) ;
rinst (N_abase b x) _ := N_abase b x ;
rinst (N_aterm t) r := N_aterm (rinst t r) ;
rinst (N_abind a) r := N_abind (rinst a (rup r)) ;
rinst (N_rinst_l xt r1) r2 := N_rinst_l xt (rcomp r1 r2) ;
rinst (N_sinst_l xt s) r := N_sinst_l xt (srcomp s r) ;
rinst (N_rinst_r i xr r1) r2 := N_rinst_r i xr (rcomp r1 r2) ;
rinst (N_sinst_r i xs s) r := N_sinst_r i xs (srcomp s r)

(** Compose a normal form substitution with a normal form renaming. *)
with srcomp : nf_subst -> nf_ren -> nf_subst :=
srcomp (N_sshift k) r := N_sren (rdrop k r) ;
srcomp (N_scons t s) r := N_scons (rinst t r) (srcomp s r) ;
srcomp (N_scomp k xs s) r := N_scomp k xs (srcomp s r) ; 
srcomp (N_sren r1) r2 := N_sren (rcomp r1 r2).

Lemma rinst_srcomp_sound_aux : 
  (forall k (t : nf_expr (Km k)) r, 
    denote_nf (rinst t r) = O.rename (denote_nf t) (denote_nf r)) *
  (forall s r, 
    denote_nf (srcomp s r) =₁ fun i => O.rename (denote_nf s i) (denote_nf r)).
Proof.
apply rinst_elim with 
  (P := fun k (t : nf_expr (Km k)) (r : nf_ren) (res : nf_expr (Km k))  => 
    denote_nf res = O.rename (denote_nf t) (denote_nf r))
  (P0 := fun (s : nf_subst) (r : nf_ren) (res : nf_subst) =>
    denote_nf res =₁ fun i => O.rename (denote_nf s i) (denote_nf r)).
- intros i r. simp denote_nf rename. now rewrite rapply_sound.
- intros c al r H. simp denote_nf. rewrite H. now simp rename.
- intros r. now simp denote_nf rename.
- intros ty tys a al r H1 H2. simp denote_nf rename. now rewrite H1, H2.
- intros b x r. now simp denote_nf rename.
- intros t r H. simp denote_nf rename. now rewrite H.
- intros ty a r H. simp denote_nf rename. now rewrite H, rup_sound.
- intros k xt r1 r2. destruct k ; simp denote_nf.
  all: now rewrite rcomp_sound, O.ren_ren.
- intros k xt s r H. destruct k ; simp denote_nf.
  all: now rewrite H, O.subst_ren.
- intros i xr r1 r2. simp denote_nf rename. f_equal. cbv [O.rcomp].
  now rewrite rcomp_sound.
- intros i xs s r H. simp denote_nf substitute. cbv [O.scomp]. 
  now rewrite H, O.subst_ren.
- intros k r. simp denote_nf. intros i. rewrite rdrop_sound. reflexivity.
- intros t s r H1 H2. simp denote_nf. rewrite H1, H2. intros [|i] ; reflexivity.
- intros k xs s r H. simp denote_nf. rewrite H. intros i. cbv [O.scomp O.sshift].
  simp substitute. now rewrite O.subst_ren.
- intros r1 r2. simp denote_nf. intros i. simp rename. now rewrite rcomp_sound.
Qed.

Lemma rinst_sound k (t : nf_expr (Km k)) r :   
  denote_nf (rinst t r) = O.rename (denote_nf t) (denote_nf r).
Proof. now apply rinst_srcomp_sound_aux. Qed.

Lemma srcomp_sound s r :
  denote_nf (srcomp s r) =₁ fun i => O.rename (denote_nf s i) (denote_nf r).
Proof. now apply rinst_srcomp_sound_aux. Qed.

(** Apply a normal form substitution to a de Bruijn index. *)
Equations sapply : nf_subst -> nat -> nf_term :=
sapply (N_sshift k) i := N_tvar (k + i) ;
sapply (N_scons t _) 0 := t ;
sapply (N_scons _ s) (S i) := sapply s i ;
sapply (N_scomp k xs s) i := N_sinst_r (k + i) xs s ;
sapply (N_sren r) i := N_tvar (rapply r i).  

Lemma sapply_sound s i : denote_nf (sapply s i) = denote_nf s i.
Proof. 
funelim (sapply s i) ; simp denote_nf ; try reflexivity.
- now rewrite H.
- now rewrite rapply_sound.
Qed.    

(** Tail of a normal form substitution. *)
Equations stail : nf_subst -> nf_subst :=
stail (N_sshift k) := N_sshift (S k) ;
stail (N_scons t s) := s ;
stail (N_scomp k xs s) := N_scomp (S k) xs s ;
stail (N_sren r) := N_sren (rtail r).

Lemma stail_sound s : denote_nf (stail s) =₁ O.scomp (O.sshift 1) (denote_nf s).
Proof. 
funelim (stail s) ; simp denote_nf.
- now rewrite O.sshift_succ_l.
- now rewrite O.sshift_scons.
- repeat rewrite <-O.scomp_assoc. now rewrite O.sshift_succ_l.
- intros i. now rewrite rtail_sound.
Qed.

(** Drop the first [k] elements in a normal form substitution. *)
Equations sdrop : nat -> nf_subst -> nf_subst :=
sdrop 0 s := s ;
sdrop (S k) s := stail (sdrop k s).

Lemma sdrop_sound k s : denote_nf (sdrop k s) =₁ O.scomp (O.sshift k) (denote_nf s).
Proof.
funelim (sdrop k s) ; simp denote_nf.
- now rewrite O.scomp_sid_l.
- rewrite stail_sound, H. now rewrite <-O.scomp_assoc, O.sshift_succ_l.
Qed.  

(** Lift a normal form substitution through a binder. *)
Equations sup : nf_subst -> nf_subst :=
sup s := N_scons (N_tvar 0) (srcomp s (N_rshift 1)).

Lemma sup_sound s : denote_nf (sup s) =₁ O.up_subst (denote_nf s).
Proof. simp sup denote_nf. unfold O.up_subst. now rewrite srcomp_sound. Qed.

(** Compose a normal form renaming with a normal form substitution. *)
Equations rscomp : nf_ren -> nf_subst -> nf_subst :=
rscomp (N_rshift k) s := sdrop k s ;
rscomp (N_rcons i r) s := N_scons (sapply s i) (rscomp r s) ;
rscomp (N_rcomp k xr r) s := N_scomp k (fun i => O.E_var (xr i)) (rscomp r s).

Lemma rscomp_sound r s : 
  denote_nf (rscomp r s) =₁ fun i => denote_nf s (denote_nf r i).
Proof.
funelim (rscomp r s) ; simp denote_nf.
- now rewrite sdrop_sound.
- rewrite sapply_sound, H. intros [|] ; reflexivity.
- now rewrite H.
Qed.     

(*(** Size of a normal form expression, not counting [N_sren]. *)
Equations nf_size {k} : nf_expr k -> nat :=
nf_size (N_tvar _) := 0 ;
nf_size (N_tctor _ al) := S (nf_size al) ;
nf_size N_al_nil := 0 ;
nf_size (N_al_cons a al) := S (nf_size a + nf_size al) ;
nf_size (N_abase _ _) := 0 ;
nf_size (N_aterm t) := S (nf_size t) ;
nf_size (N_abind a) := S (nf_size a) ;

nf_size (N_rshift _) := 0 ;
nf_size (N_rcons _ r) := S (nf_size r) ;
nf_size (N_rcomp _ _ r) := S (nf_size r) ;

nf_size (N_sshift _) := 0 ;
nf_size (N_scons t s) := S (nf_size t + nf_size s) ;
nf_size (N_scomp _ _ s) := S (nf_size s) ;
(** We explicitly don't increase the size when going through [N_sren]. *)
nf_size (N_sren r) := nf_size r ;

nf_size (N_rinst_l _ r) := S (nf_size r) ;
nf_size (N_sinst_l _ s) := S (nf_size s) ;
nf_size (N_rinst_r _ _ r) := S (nf_size r) ;
nf_size (N_sinst_r _ _ s) := S (nf_size s).*)

(** Instantiate a normal form expression with a normal form substitution. *)
Equations sinst {k} (t : nf_expr (Km k)) (s : nf_subst) : nf_expr (Km k) by struct t :=
sinst (N_tvar i) s := sapply s i ;
sinst (N_tctor c al) s := N_tctor c (sinst al s) ;
sinst N_al_nil _ := N_al_nil ;
sinst (N_al_cons a al) s := N_al_cons (sinst a s) (sinst al s) ;
sinst (N_abase b x) _ := N_abase b x ;
sinst (N_aterm t) s := N_aterm (sinst t s) ;
sinst (N_abind a) s := N_abind (sinst a (sup s)) ;
sinst (N_rinst_l xt r) s := N_sinst_l xt (rscomp r s) ;
sinst (N_sinst_l xt s1) s2 := N_sinst_l xt (scomp s1 s2) ;
sinst (N_rinst_r i xr r) s := N_sinst_r i (fun i => O.E_var (xr i)) (rscomp r s) ;
sinst (N_sinst_r i xs s1) s2 := N_sinst_r i xs (scomp s1 s2)

(** Compose two normal form substitutions. *)
with scomp (s1 : nf_subst) (s2 : nf_subst) : nf_subst by struct s1 :=
scomp (N_sshift k) s := sdrop k s ;
scomp (N_scons t s1) s2 := N_scons (sinst t s1) (scomp s1 s2) ;
scomp (N_scomp k xs s1) s2 := N_scomp k xs (scomp s1 s2) ; 
scomp (N_sren r) s := rscomp r s.

Lemma sinst_scomp_sound_aux : 
  (forall k (t : nf_expr (Km k)) s, 
    denote_nf (sinst t s) = O.substitute (denote_nf t) (denote_nf s)) *
  (forall s1 s2, 
    denote_nf (scomp s1 s2) =₁ O.scomp (denote_nf s1) (denote_nf s2)).
Proof.
apply sinst_elim with 
  (P := fun k (t : nf_expr (Km k)) (s : nf_subst) (res : nf_expr (Km k))  => 
    denote_nf res = O.substitute (denote_nf t) (denote_nf s))
  (P0 := fun (s1 s2 res : nf_subst) =>
    denote_nf res =₁ O.scomp (denote_nf s1) (denote_nf s2)).
- intros i s. now rewrite sapply_sound.
- intros c al s H. simp denote_nf. now rewrite H.
- reflexivity.
- intros ty tys a al s H1 H2. simp denote_nf substitute. now rewrite H1, H2.
- intros b x s. now simp denote_nf substitute.
- intros t s H. simp denote_nf substitute. now rewrite H.
- intros ty a s H. simp denote_nf substitute. now rewrite H, sup_sound.
- intros k xt r s. destruct k ; simp denote_nf substitute.
  all: now rewrite rscomp_sound, O.ren_subst.
- intros k xt s1 s2 H. destruct k ; simp denote_nf substitute.
  all: now rewrite H, O.subst_subst.
- intros i xr r s. simp denote_nf substitute rename.
  cbv [O.scomp]. simp substitute. now rewrite rscomp_sound.
- intros i xs s1 s2 H. simp denote_nf substitute. 
  cbv [O.scomp]. now rewrite H, O.subst_subst.
- intros k s. simp denote_nf. now rewrite sdrop_sound.
- intros t s1 s2 H1 H2. simp denote_nf substitute.           


    