From Prototype Require Import Prelude Sig LevelOne.

Module Make (S : Sig).
Module O := LevelOne.Make (S).

Local Coercion is_true : bool >-> Sortclass.

(** Meta-variables are represented by an index (a natural). *)
Definition mvar := nat.

(*********************************************************************************)
(** *** Quoted naturals and explicit renamings. *)
(*********************************************************************************)

(** Quoted natural. *)
Inductive qnat :=
(** Zero. *)
| Q_zero : qnat
(** Explicit renaming applied to a quoted natural. *)
| Q_rapply : ren -> qnat -> qnat 
(** Quoted natural meta-variable. *)
| Q_mvar : mvar -> qnat

(** Explicit renaming. *)
with ren :=
(** Identity renaming. *)
| R_id : ren
(** Explicit shift. *)
| R_shift : ren
(** Renaming expansion. *)
| R_cons : qnat -> ren -> ren
(** Left to right composition of renamings. *)
| R_comp : ren -> ren -> ren 
(** Renaming meta-variable. *)
| R_mvar : mvar -> ren.

(*********************************************************************************)
(** *** Expressions and explicit substitutions. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Expressions are indexed by a kind: this is to avoid having too many 
    distinct constructors for instantiation by a renaming/substitution. *)
Inductive expr : kind -> Type :=

(** Variable term constructor (de Bruijn index). *)
| E_tvar : qnat -> term
(** Non-variable term constructor, applied to a list of arguments. *)
| E_tctor : forall c, args (ctor_type S.t c) -> term
(** Term metavariable. We don't need argument or argument-list metavariables. *)
| E_mvar : mvar -> term

(** Empty argument list. *)
| E_al_nil : args []
(** Non-empty argument list. *)
| E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

(** Base argument (e.g. bool or string). *)
| E_abase : forall b, denote_base S.t b -> arg (AT_base b)
(** Term argument. *)
| E_aterm : term -> arg AT_term
(** Binder argument. *)
| E_abind {ty} : arg ty -> arg (AT_bind ty)

(** Instantiate an expressions with a renaming. *)
| E_ren {k} : expr k -> ren -> expr k
(** Instantiate an expressions with a substitution. *)
| E_subst {k} : expr k -> subst -> expr k

with subst :=
(** Identity substitution. *)
| S_id : subst
(** Shift substitution. *)
| S_shift : subst
(** Substitution expansion. *)
| S_cons : term -> subst -> subst
(** Left to right composition of substitutions. *)
| S_comp : subst -> subst -> subst
(** View a renaming as a substitution. *)
| S_ren : ren -> subst
(** Substitution metavariable. *)
| S_mvar : mvar -> subst

where "'term'" := (expr Kt)
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

(*********************************************************************************)
(** *** Evaluation. *)
(*********************************************************************************)

(** An environment is a mapping from meta-variables to level one expressions. *)
Record env := 
  { assign_qnat : mvar -> nat
  ; assign_ren : mvar -> O.ren 
  ; assign_term : mvar -> O.expr Kt
  ; assign_subst : mvar -> O.subst }. 

Section Evaluation.
  Context (e : env).

  Equations qeval : qnat -> nat :=
  qeval Q_zero := 0 ;
  qeval (Q_rapply r i) := reval r (qeval i) ;
  qeval (Q_mvar x) := e.(assign_qnat) x
  
  with reval : ren -> O.ren :=
  reval R_id := O.rid ;
  reval R_shift := O.rshift ;
  reval (R_cons i r) := O.rcons (qeval i) (reval r) ;
  reval (R_comp r1 r2) := O.rcomp (reval r1) (reval r2) ;
  reval (R_mvar x) := e.(assign_ren) x.

  Equations eeval {k} : expr k -> O.expr k :=
  eeval (E_tvar i) := O.E_var (qeval i) ;
  eeval (E_tctor c al) := O.E_ctor c (eeval al) ;
  eeval E_al_nil := O.E_al_nil ;
  eeval (E_al_cons a al) := O.E_al_cons (eeval a) (eeval al) ;
  eeval (E_abase b x) := O.E_abase b x ;
  eeval (E_aterm t) := O.E_aterm (eeval t) ;
  eeval (E_abind a) := O.E_abind (eeval a) ;
  eeval (E_ren e r) := O.rename (eeval e) (reval r) ;
  eeval (E_subst e s) := O.substitute (eeval e) (seval s) ;
  eeval (E_mvar x) := e.(assign_term) x
  
  with seval : subst -> O.subst :=
  seval S_id := O.sid ;
  seval S_shift := O.sshift ;
  seval (S_cons t s) := O.scons (eeval t) (seval s) ;
  seval (S_comp s1 s2) := O.scomp (seval s1) (seval s2) ;
  seval (S_ren r) := O.rscomp (reval r) O.E_var ;
  seval (S_mvar x) := e.(assign_subst) x.

End Evaluation.
 
(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

(** Turn an Ltac2 [int] to a Rocq [nat]. 
    Negative integers are mapped to [0]. *)
Ltac2 rec nat_of_int (x : int) : constr := 
  if Int.le x 0 then constr:(0)
  else let y := nat_of_int (Int.sub x 1) in constr:(S $y).

(** Reification environment. *)
Ltac2 Type env := 
  { qnat_mvars : constr list 
  ; ren_mvars : constr list
  ; term_mvars : constr list
  ; subst_mvars : constr list }.

Ltac2 empty_env () := 
  { qnat_mvars := [] ; ren_mvars := [] ; term_mvars := [] ; subst_mvars := [] }.

Ltac2 add_qnat_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := List.append (e.(qnat_mvars)) [t] 
  ; ren_mvars := e.(ren_mvars)
  ; term_mvars := e.(term_mvars)
  ; subst_mvars := e.(subst_mvars) }.
  
Ltac2 add_ren_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := e.(qnat_mvars) 
  ; ren_mvars := List.append (e.(ren_mvars)) [t]
  ; term_mvars := e.(term_mvars)
  ; subst_mvars := e.(subst_mvars) }.

Ltac2 add_term_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := e.(qnat_mvars) 
  ; ren_mvars := e.(ren_mvars)
  ; term_mvars := List.append (e.(term_mvars)) [t]
  ; subst_mvars := e.(subst_mvars) }.

Ltac2 add_subst_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := e.(qnat_mvars) 
  ; ren_mvars := e.(ren_mvars)
  ; term_mvars := e.(term_mvars)
  ; subst_mvars := List.append (e.(subst_mvars)) [t] }.

(* TODO: handle renamings directly applied to naturals. *)
Ltac2 rec reify_nat (e : env) (t : constr) : env * constr := 
  lazy_match! t with 
  | 0 => e, constr:(Q_zero)
  | S ?i =>
    let (e, i) := reify_nat e i in 
    e, constr:(Q_rapply R_shift $i)
  | ?r ?i =>
    let (e, r) := reify_ren e r in
    let (e, i) := reify_nat e i in
    e, constr:(Q_rapply $r $i)
  | ?i => 
    let idx := nat_of_int (List.length (e.(qnat_mvars))) in
    let e := add_qnat_mvar i e in
    e, constr:(Q_mvar $idx)
  end

with reify_ren (e : env) (t : constr) : env * constr :=
  lazy_match! t with 
  | O.rid => e, constr:(R_id)
  | O.rshift => e, constr:(R_shift) 
  | O.rcons ?i ?r =>
    let (e, i) := reify_nat e i in 
    let (e, r) := reify_ren e r in 
    e, constr:(R_cons $i $r)
  | O.rcomp ?r1 ?r2 =>
    let (e, r1) := reify_ren e r1 in 
    let (e, r2) := reify_ren e r2 in 
    e, constr:(R_comp $r1 $r2)
  | ?r => 
    let idx := nat_of_int (List.length (e.(ren_mvars))) in 
    let e := add_ren_mvar r e in
    e, constr:(R_mvar $idx)
  end.

Ltac2 rec reify_expr (e : env) (t : constr) : env * constr :=
  lazy_match! t with 
  | O.E_var ?i => 
    let (e, i) := reify_nat e i in
    e, constr:(E_tvar $i)
  | O.E_ctor ?c ?al => 
    let (e, al) := reify_expr e al in
    e, constr:(E_tctor $c $al)
  | O.E_al_nil => e, constr:(E_al_nil)
  | O.E_al_cons ?a ?al => 
    let (e, a) := reify_expr e a in
    let (e, al) := reify_expr e al in
    e, constr:(E_al_cons $a $al)
  | O.E_abase ?b ?x => e, constr:(E_abase $b $x)
  | O.E_aterm ?t => 
    let (e, t) := reify_expr e t in
    e, constr:(E_aterm $t)
  | O.E_abind ?a =>
    let (e, a) := reify_expr e a in
    e, constr:(E_abind $a)
  | O.rename ?t ?r =>
    let (e, t) := reify_expr e t in
    let (e, r) := reify_ren e r in
    e, constr:(E_ren $t $r)
  | O.substitute ?t ?s =>
    let (e, t) := reify_expr e t in
    let (e, s) := reify_subst e s in
    e, constr:(E_subst $t $s)
  | ?t => 
    let idx := nat_of_int (List.length (e.(term_mvars))) in
    let e := add_term_mvar t e in
    e, constr:(E_mvar $idx)
  end

with reify_subst (e : env) (s : constr) : env * constr :=
  lazy_match! s with 
  | O.sid => e, constr:(S_id)
  | O.sshift => e, constr:(S_shift)
  | O.scons ?t ?s =>
    let (e, t) := reify_expr e t in 
    let (e, s) := reify_subst e s in 
    e, constr:(S_cons $t $s)
  | O.scomp ?s1 ?s2 =>
    let (e, s1) := reify_subst e s1 in 
    let (e, s2) := reify_subst e s2 in 
    e, constr:(S_comp $s1 $s2)
  | O.srcomp ?s ?r =>
    let (e, s) := reify_subst e s in 
    let (e, r) := reify_ren e r in
    e, constr:(S_comp $s (S_ren $r))
  | O.rscomp ?r ?s =>
    let (e, r) := reify_ren e r in
    let (e, s) := reify_subst e s in 
    e, constr:(S_comp (S_ren $r) $s)
  | ?s => 
    let idx := nat_of_int (List.length (e.(subst_mvars))) in
    let e := add_subst_mvar s e in
    e, constr:(S_mvar $idx)
  end.

(*********************************************************************************)
(** *** Discriminators. *)
(*********************************************************************************)

(** Simplification needs to distinguish terms based on their head constructor(s). 
    We provide discriminator functions which handle this. *)

Definition is_qrapply x := 
  match x with Q_rapply _ _ => true | _ => false end.
Definition is_qmvar x :=
  match x with Q_mvar _ => true | _ => false end.

Definition is_rcons r := 
  match r with R_cons _ _ => true | _ => false end.
Definition is_rcomp r := 
  match r with R_comp _ _ => true | _ => false end.
Definition is_rmvar r := 
  match r with R_mvar _ => true | _ => false end. 

Definition is_rid_l r := 
  match r with R_comp R_id _ => true | _ => false end.
Definition is_rshift_l r := 
  match r with R_comp R_shift _ => true | _ => false end.
Definition is_rcons_l r := 
  match r with R_comp (R_cons _ _) _ => true | _ => false end. 
Definition is_rcomp_l r := 
  match r with R_comp (R_comp _ _) _ => true | _ => false end.
Definition is_rmvar_l r := 
  match r with R_comp (R_mvar _) _ => true | _ => false end.

Definition is_tvar {k} (t : expr k) :=
  match t with E_tvar _ => true | _ => false end.
Definition is_tvar_zero {k} (t : expr k) :=
  match t with E_tvar Q_zero => true | _ => false end.
Definition is_tmvar {k} (e : expr k) :=
  match e with E_mvar _ => True | _ => False end.

Definition is_scons s :=
  match s with S_cons _ _ => true | _ => false end.
Definition is_scomp s :=
  match s with S_comp _ _ => true | _ => false end.
Definition is_smvar s :=
  match s with S_mvar _ => true | _ => false end.
Definition is_sren s := 
  match s with S_ren _ => true | _ => false end.

Definition is_scons_l s :=
  match s with S_comp (S_cons _ _) _ => true | _ => false end.
Definition is_scomp_l s :=
  match s with S_comp (S_comp _ _) _ => true | _ => false end.
Definition is_smvar_l s :=
  match s with S_comp (S_mvar _) _ => true | _ => false end.
Definition is_sren_l s := 
  match s with S_comp (S_ren _) _ => true | _ => false end.

(*********************************************************************************)
(** *** Irreducible forms for renamings & naturals. *)
(*********************************************************************************)

(** Reducible quoted naturals. *)
Inductive qred : qnat -> Prop :=

(** Congruence. *)
| QR_ren r x : rred r \/ qred x -> qred (Q_rapply r x)

| QR_ren_ren r1 r2 i : qred (Q_rapply r1 (Q_rapply r2 i))
| QR_ren_id i : qred (Q_rapply R_id i)
| QR_rcons_zero r : 
    is_rcons r \/ is_rcons_l r -> qred (Q_rapply r Q_zero)

(** Reducible renamings. *)
with rred : ren -> Prop :=

(** Congruence. *)
| RR_cons i r : qred i \/ rred r -> rred (R_cons i r)
| RR_comp r1 r2 : rred r1 \/ rred r2 -> rred (R_comp r1 r2)

(** Composition should be right associated, with neutral element [R_id]. *)
| RR_rid_l r : rred (R_comp R_id r)
| RR_rid_r r : rred (R_comp r R_id)
| RR_comp_l r1 r2 r3 : rred (R_comp (R_comp r1 r2) r3)

| RR_cons_l i r1 r2 : rred (R_comp (R_cons i r1) r2)
| RR_shift_cons r : 
  is_rcons r \/ is_rcons_l r -> rred (R_comp R_shift r).

Hint Constructors qred : core.
Hint Constructors rred : core.

(** Irreducible quoted natural. *)
Definition qirred x := ~ qred x.

(** Irreducible renaming. *)
Definition rirred r := ~ rred r.

(*********************************************************************************)
(** *** Properties of renaming & natural irreducible forms. *)
(*********************************************************************************)

Lemma qirred_rapply_shift i : 
  qirred (Q_rapply R_shift i) <-> qirred i /\ ~is_qrapply i.
split ; intros H.
- split ; intros H' ; apply H ; clear H.
  + constructor ; now right.
  + destruct i ; triv.
- intros H'. inv H'.
  + destruct H1 ; triv.
  + destruct H ; triv.
  + destruct H1 ; triv.
Qed.

Lemma qirred_rapply_mvar m i : 
  qirred (Q_rapply (R_mvar m) i) <-> qirred i /\ ~is_qrapply i.
Proof.
split ; intros H.
- split ; intros H' ; apply H ; clear H.
  + constructor ; now right.
  + destruct i ; triv.
- intros H'. inv H'.
  + destruct H1 ; triv.
  + destruct H ; triv.
  + destruct H1 ; triv.
Qed.     

Lemma qirred_rapply_cons i r k :
  qirred (Q_rapply (R_cons i r) k) <-> qirred i /\ rirred r /\ is_qmvar k.
Proof.
split.
- intros H. split3.
  + intros H' ; apply H ; clear H. constructor ; left. constructor ; now left.
  + intros H' ; apply H ; clear H. constructor ; left. constructor ; now right. 
  + destruct k ; triv. exfalso. apply H. triv. 
- intros (H1 & H2 & H3) H. destruct k ; triv. inv H ; triv.
  destruct H4 ; triv. inv H0. destruct H5 ; triv.
Qed.

Lemma qirred_rapply r i : 
  qirred (Q_rapply r i) <-> 
    rirred r /\ qirred i /\ r <> R_id /\ ~is_qrapply i /\
    ~(is_rcons r /\ i = Q_zero).
Proof. 
split ; intros H. 
- split5 ; intros H' ; apply H ; triv.
  + destruct i ; triv.
  + destruct r ; triv. destruct H' as (_ & ->). triv.
- intros H' ; inv H' ; triv.
  + destruct H1 ; triv.
  + destruct H as (_ & _ & _ & H & _). triv.
  + destruct H1 ; destruct r ; triv.
    * destruct H as (_ & _ & _ & _ & H). triv.
    * destruct H as (H & _). destruct r1 ; triv.        
Qed.

Lemma rirred_cons i r : 
  rirred (R_cons i r) <-> qirred i /\ rirred r.
Proof.
split.
- intros H. split ; intros H' ; apply H.
  all: constructor ; auto.
- intros [H1 H2] H. inv H. destruct H3 ; auto.
Qed.

Lemma rirred_mvar_l m r : 
  rirred (R_comp (R_mvar m) r) <-> rirred r /\ r <> R_id.
Proof.
split.
- intros H. split.
  + intros H'. apply H ; clear H. apply RR_comp. now right.
  + intros H' ; subst. apply H. now constructor. 
- intros (H & H') H''. inv H'' ; triv. now destruct H1.
Qed.      

Lemma rirred_shift_l r : 
  rirred (R_comp R_shift r) <-> 
    rirred r /\ r <> R_id /\ ~is_rcons r /\ ~is_rcons_l r.
Proof.
split.
- intros H. split4 ; triv. intros H' ; apply H ; triv.
- intros (H1 & H2) H. inv H ; triv.
  + destruct H3 ; triv.
  + destruct H3 ; triv.
Qed.

Lemma rirred_comp r1 r2 : 
  rirred (R_comp r1 r2) <->
    rirred r1 /\ rirred r2 /\ ~is_rcomp r1 /\ ~is_rcons r1 /\ 
    r1 <> R_id /\ r2 <> R_id /\ ~(r1 = R_shift /\ is_rcons r2).
Proof.
split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct r1 ; triv.
  + destruct r1 ; triv.
  + destruct H' as [-> H']. destruct r2 ; triv.
- intros H' ; inv H' ; triv.
  + destruct H1 ; triv.
  + destruct H as (_ & _ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _) ; triv.
  + destruct H1 ; destruct r2 ; triv.
    * destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
    * destruct r2_1 ; triv. destruct H as (_ & H & _). triv.
Qed. 

(*********************************************************************************)
(** *** Simplification of renamings & quoted naturals. *)
(*********************************************************************************)

(** Helper function for [rapply] which takes care of trivial cases. *)
Equations rapply_aux (r : ren) (i : qnat) : qnat :=
rapply_aux R_id i := i ;
rapply_aux (R_cons k r) Q_zero := k ;
rapply_aux r i := Q_rapply r i.

Lemma rapply_aux_sound e r i : 
  qeval e (rapply_aux r i) = reval e r (qeval e i).
Proof. funelim (rapply_aux r i) ; simp qeval ; triv. Qed.
#[global] Hint Rewrite rapply_aux_sound : qeval.

Lemma rapply_aux_irred r i : 
  rirred r -> qirred i -> 
  (r <> R_id -> ~(is_rcons r /\ i = Q_zero) -> qirred (Q_rapply r i)) -> 
  qirred (rapply_aux r i).
Proof.
intros H1 H2 H3. funelim (rapply_aux r i) ; triv.
all: try solve [ apply H3 ; triv ].
rewrite rirred_cons in H1 ; triv.
Qed.   

(** Helper function for [rcomp] which takes care of trivial cases. *)
Equations rcomp_aux (r1 r2 : ren) : ren :=
rcomp_aux r R_id := r ;
rcomp_aux R_shift (R_cons _ r) := r ;
rcomp_aux r1 r2 := R_comp r1 r2.

Lemma rcomp_aux_sound e r1 r2 :
  reval e (rcomp_aux r1 r2) =₁ O.rcomp (reval e r1) (reval e r2).
Proof. funelim (rcomp_aux r1 r2) ; simp qeval ; triv. Qed.
#[global] Hint Rewrite rcomp_aux_sound : qeval reval.

Lemma rcomp_aux_irred r1 r2 : 
  rirred r1 -> rirred r2 -> 
  (r2 <> R_id -> ~(r1 = R_shift /\ is_rcons r2) -> rirred (R_comp r1 r2)) -> 
  rirred (rcomp_aux r1 r2).
Proof.
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; triv.
all: try solve [ apply H3 ; now triv ].
now rewrite rirred_cons in H2.
Qed.

(** Apply an irreducible renaming to an irreducible quoted natural. *)
Equations rapply (r : ren) (i : qnat) : qnat by struct i := 
rapply r (Q_rapply r' i) := rapply_aux (rcomp r' r) i ;
rapply r i := rapply_aux r i

(** Compose two irreducible renamings. *)
with rcomp (r1 r2 : ren) : ren by struct r1 :=
rcomp R_id r := r ;
rcomp (R_cons i r1) r2 := R_cons (rapply r2 i) (rcomp r1 r2) ;
rcomp (R_comp r1 r2) r3 := rcomp r1 (rcomp r2 r3) ;
rcomp r1 r2 := rcomp_aux r1 r2.

Lemma rapply_rcomp_sound e :
  (forall r i, qeval e (rapply r i) = reval e r (qeval e i)) * 
  (forall r1 r2, reval e (rcomp r1 r2) =₁ O.rcomp (reval e r1) (reval e r2)).
Proof.
apply rapply_elim with 
  (P := fun r i res => qeval e res = reval e r (qeval e i))
  (P0 := fun r1 r2 res => reval e res =₁ O.rcomp (reval e r1) (reval e r2)).
all: intros ; simp qeval reval ; triv.
- rewrite H, H0. now rewrite O.rcomp_rcons_distrib.
- rewrite H0, H. now rewrite O.rcomp_assoc.
Qed.

Lemma rapply_sound e r i : 
  qeval e (rapply r i) = reval e r (qeval e i).
Proof. now apply rapply_rcomp_sound. Qed.
#[global] Hint Rewrite rapply_sound : qeval reval.

Lemma rcomp_sound e r1 r2 :
  reval e (rcomp r1 r2) =₁ O.rcomp (reval e r1) (reval e r2).
Proof. now apply rapply_rcomp_sound. Qed.
#[global] Hint Rewrite rcomp_sound : qeval reval.

Lemma rapply_rcomp_irred :
  (forall r i, rirred r -> qirred i -> qirred (rapply r i)) *
  (forall r1 r2, rirred r1 -> rirred r2 -> rirred (rcomp r1 r2)).
Proof.
apply rapply_elim with 
  (P := fun r i res => rirred r -> qirred i -> qirred res)
  (P0 := fun r1 r2 res => rirred r1 -> rirred r2 -> rirred res).
all: intros ; triv.
- apply rapply_aux_irred ; triv. intros H1 H2. rewrite qirred_rapply.
  split5 ; triv.
- rewrite qirred_rapply in H1. apply rapply_aux_irred ; triv. 
  + now apply H.
  + intros H2 H3. rewrite qirred_rapply. split5 ; triv. now apply H.
- apply rapply_aux_irred ; triv. intros H1 H2. rewrite qirred_rapply.
  split5 ; triv.
- apply rcomp_aux_irred ; triv. intros H1 H2. rewrite rirred_shift_l.
  split4 ; triv. destruct r2 ; triv. destruct r2_1 ; triv.
- rewrite rirred_cons in *. split.
  + now apply H.
  + now apply H0.
- assert (H3 : rirred r1 /\ rirred r2).
  { split ; intros H' ; apply H1 ; triv. }
  apply H0 ; triv. apply H ; triv.
- apply rcomp_aux_irred ; triv. intros H1 H2. rewrite rirred_mvar_l.
  split ; triv.
Qed. 

(** Simplify a quoted natural. *)
Equations qsimp : qnat -> qnat :=
qsimp Q_zero := Q_zero ;
qsimp (Q_rapply r i) := rapply (rsimp r) (qsimp i) ;
qsimp (Q_mvar m) := Q_mvar m 

(** Simplify a renaming. *)
with rsimp : ren -> ren :=
rsimp (R_cons i r) := R_cons (qsimp i) (rsimp r) ;
rsimp (R_comp r1 r2) := rcomp (rsimp r1) (rsimp r2) ;
rsimp r := r.

Lemma qsimp_rsimp_sound e :
  (forall i, qeval e (qsimp i) = qeval e i) *
  (forall r, reval e (rsimp r) =₁ reval e r).
Proof. 
apply qsimp_elim with 
  (P := fun i res => qeval e res = qeval e i)
  (P0 := fun r res => reval e res =₁ reval e r).
all: intros ; simp qeval reval ; triv.
- now rewrite H, H0.
- now rewrite H, H0.
- now rewrite H, H0. 
Qed.    

Lemma qsimp_sound e i : qeval e (qsimp i) = qeval e i.
Proof. now apply qsimp_rsimp_sound. Qed.
#[global] Hint Rewrite qsimp_sound : qeval.

Lemma rsimp_sound e r : reval e (rsimp r) =₁ reval e r.
Proof. now apply qsimp_rsimp_sound. Qed.
#[global] Hint Rewrite rsimp_sound : qeval reval.

Lemma qsimp_rsimp_irred : 
  (forall i, qirred (qsimp i)) * (forall r, rirred (rsimp r)).
Proof.
apply qsimp_elim with (P := fun _ res => qirred res) (P0 := fun _ res => rirred res).
all: intros ; triv.
- now apply rapply_rcomp_irred.
- now rewrite rirred_cons.
- now apply rapply_rcomp_irred.
Qed.

Lemma qsimp_irred i : qirred (qsimp i).
Proof. now apply qsimp_rsimp_irred. Qed.

Lemma rsimp_irred r : rirred (rsimp r).
Proof. now apply qsimp_rsimp_irred. Qed.
  
(*********************************************************************************)
(** *** Irreducible forms for substitutions & expressions. *)
(*********************************************************************************)

(** Expressions in which we can push renamings. *)
Definition is_push_ren {k} (e : expr k) : Prop :=
  match e with E_mvar _ => False | _ => True end.

(** Expressions in which we can push substitutions. *)
Definition is_push_subst {k} (e : expr k) : Prop :=
  match e with E_mvar _ | E_tvar _ => False | _ => True end.

(** Reducible expression. *)
Inductive ered : forall {k}, expr k -> Prop :=

(** Congruence. *)
| ER_tvar i : qred i -> ered (E_tvar i)
| ER_tctor c al : ered al -> ered (E_tctor c al)
| ER_al_cons {ty} {tys} (a : arg ty) (al : args tys) : 
    ered a \/ ered al -> ered (E_al_cons a al)
| ER_aterm t : ered t -> ered (E_aterm t)
| ER_abind {ty} (a : arg ty) : ered a -> ered (E_abind a) 
| ER_ren {k} r (e : expr k) : rred r \/ ered e -> ered (E_ren e r)
| ER_subst {k} s (e : expr k) : sred s \/ ered e -> ered (E_subst e s)

(** Push renamings/substitutions inside expressions. *)
| ER_push_ren {k} r (e : expr k) : is_push_ren e -> ered (E_ren e r)
| ER_push_subst {k} s (e : expr k) : is_push_subst e -> ered (E_subst e s)

(** Identity renaming/substitution. *)
| ER_ren_rid {k} (e : expr k) : ered (E_ren e R_id)
| ER_subst_sid {k} (e : expr k) : ered (E_subst e S_id)

(** Apply a substitution/renaming to a variable. *)
| ER_scons_zero s : 
    is_scons s \/ is_scons_l s -> ered (E_subst (E_tvar Q_zero) s)
| ER_sren_var s r i : 
    ered (E_subst (E_tvar (Q_rapply r i)) s)

(** Substitute with a renaming. *)
| ER_subst_ren {k} (e : expr k) r : ered (E_subst e (S_ren r))

(** Reducible substitutions. *)
with sred : subst -> Prop :=

(** Congruence. *)
| SR_cons t s : ered t \/ sred s -> sred (S_cons t s)
| SR_comp s1 s2 : sred s1 \/ sred s2 -> sred (S_comp s1 s2)
| SR_ren r : rred r -> sred (S_ren r)

(** Composition should be right associated, with neutral element [S_id]. *)
| SR_sid_l s : sred (S_comp S_id s)
| SR_sid_r s : sred (S_comp s S_id)
| SR_comp_l s1 s2 s3: sred (S_comp (S_comp s1 s2) s3)

(** Push [S_ren] into renamings. *)
| SR_ren_distrib r : ~is_rmvar r -> sred (S_ren r)
(** Composition distributes over [S_cons]. *)
| SR_cons_l t s1 s2 : sred (S_comp (S_cons t s1) s2)
(** Simplify [shift >> (t . s)] into [s]. *)
| SR_shift_cons s : 
  is_scons s \/ is_scons_l s -> sred (S_comp S_shift s).

Hint Constructors ered : core.
Hint Constructors sred : core.

(** Irreducible expression. *)
Definition eirred {k} (e : expr k) := ~ered e.

(** Irreducible substitution. *)
Definition sirred s := ~sred s.

(*********************************************************************************)
(** *** Properties of substitution & expression irreducible forms. *)
(*********************************************************************************)

Lemma eirred_tvar i : eirred (E_tvar i) <-> qirred i.
Proof. split ; intros H H' ; apply H ; triv. now inv H'. Qed.

Lemma eirred_tctor c al : eirred (E_tctor c al) <-> eirred al.
Proof. split ; intros H H' ; apply H ; triv. now inv H'. Qed.

Lemma eirred_al_nil : eirred E_al_nil.
Proof. intros H ; inv H. Qed.

Lemma eirred_al_cons {ty tys} (a : arg ty) (al : args tys) :
  eirred (E_al_cons a al) <-> eirred a /\ eirred al.
Proof.
split ; intros H.
- split ; intros H' ; apply H ; triv.
- intros H' ; inv H' ; triv. destruct H1 ; triv.
Qed.

Lemma eirred_abase b x : eirred (E_abase b x).
Proof. triv. Qed.

Lemma eirred_aterm t : eirred (E_aterm t) <-> eirred t.
Proof. split ; intros H H' ; apply H ; triv. now inv H'. Qed.

Lemma eirred_abind {ty} (a : arg ty) : 
  eirred (E_abind a) <-> eirred a.
Proof. split ; intros H H' ; apply H ; triv. now inv H'. Qed.

Lemma eirred_ren {k} (e : expr k) r :
  eirred (E_ren e r) <-> is_tmvar e /\ rirred r /\ r <> R_id.
Proof.
split ; intros H.
- split3.
  + destruct e ; triv.
  + intros H' ; apply H ; triv.
  + intros H' ; apply H ; triv.
- intros H' ; inv H' ; triv.
  + destruct H2 ; triv. destruct e ; triv.
  + destruct e ; triv.
Qed.

Lemma eirred_subst_var s i :
  eirred (E_subst (E_tvar i) s) <->
    qirred i /\ sirred s /\ ~(i = Q_zero /\ is_scons s) /\ s <> S_id /\ 
    ~is_sren s /\ ~is_qrapply i.
Proof.
split ; intros H.
- split6 ; intros H' ; apply H ; clear H ; triv.
  + destruct H' as [-> H']. triv.
  + destruct s ; triv.
  + destruct i ; triv.
- destruct H as (H1 & H2 & H3 & H4 & H5 & H6). intros H' ; inv H' ; triv.
  + destruct H7 ; triv. now inv H.
  + destruct H7 ; triv. destruct s ; triv. destruct s1 ; triv.
Qed.

Definition is_tvar_rapply {k} (e : expr k) := 
  match e with 
  | E_tvar (Q_rapply _ _) => true 
  | _ => false
  end.

Lemma eirred_subst {k} (e : expr k) s :
  eirred (E_subst e s) <->
    eirred e /\ sirred s /\ ~is_push_subst e /\ ~is_tvar_rapply e /\
    ~(is_tvar_zero e /\ is_scons s) /\ s <> S_id /\ ~is_sren s.
Proof.
split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct e ; triv. destruct q ; triv.
  + destruct e ; triv. destruct q ; triv. destruct s ; triv.
  + destruct s ; triv.
- intros H' ; inv H' ; triv.
  + destruct H2 ; triv.
  + destruct H2 ; destruct s ; try discriminate.
    * destruct H as (_ & _ & _ & _ & H & _). triv.
    * destruct s1 ; triv. destruct H as (_ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _). triv.
  + destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
Qed.     

Lemma sirred_cons t s : 
  sirred (S_cons t s) <-> eirred t /\ sirred s.
Proof.
split ; intros H.
- split ; intros H' ; apply H ; clear H.
  + constructor ; now left.
  + constructor ; now right.
- intros H'. inv H'. destruct H1 ; triv.
Qed.   

Lemma sirred_shift_l s : 
  sirred (S_comp S_shift s) <->
    sirred s /\ ~is_scons s /\ s <> S_id.
Proof.
split.
- intros H. split3 ; intros H' ; apply H ; clear H ; triv.
- intros (H1 & H2 & H3) H'. inv H' ; triv.
  + destruct H0 ; triv.
  + destruct H0 ; triv. destruct s ; triv. destruct s1 ; triv.
Qed.  

Lemma sirred_ren_l r s : 
  sirred (S_comp (S_ren r) s) <-> is_rmvar r /\ sirred s /\ s <> S_id.
Proof.
split ; intros H.
- split3.
  + destruct r ; triv. 
    all: exfalso ; apply H.
    all: constructor ; left.
    all: now apply SR_ren_distrib.
  + intros H' ; apply H ; clear H. constructor. now right.
  + intros H'. apply H ; clear H. subst. now constructor.
- intros H'. inv H' ; triv. destruct H1 ; triv. inv H0 ; triv.
  destruct r ; triv.
Qed.

Lemma sirred_mvar_l m s : 
  sirred (S_comp (S_mvar m) s) <-> sirred s /\ s <> S_id.
Proof.
split.
- intros H. split.
  + intros H'. apply H ; clear H. apply SR_comp. now right.
  + intros H' ; subst. apply H. now constructor. 
- intros (H & H') H''. inv H'' ; triv. now destruct H1.
Qed. 

Lemma sirred_ren r : sirred (S_ren r) <-> is_rmvar r.
Proof.
split ; intros H.
- destruct r ; triv. all: exfalso ; apply H ; now constructor.
- intros H' ; inv H' ; triv. destruct r ; triv.
Qed.

Lemma sirred_comp s1 s2 : 
  sirred (S_comp s1 s2) <->
    sirred s1 /\ sirred s2 /\ ~is_scomp s1 /\ ~is_scons s1 /\ 
    s1 <> S_id /\ s2 <> S_id /\ ~(s1 = S_shift /\ is_scons s2).
Proof.
split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct s1 ; triv.
  + destruct s1 ; triv.
  + destruct H' as [-> H']. destruct s2 ; triv.
- intros H' ; inv H' ; triv.
  + destruct H1 ; triv.
  + destruct H as (_ & _ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _) ; triv.
  + destruct H1 ; destruct s2 ; triv.
    * destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
    * destruct s2_1 ; triv. destruct H as (_ & H & _). triv.
Qed. 

(*********************************************************************************)
(** *** Simplify substitutions & expressions. *)
(*********************************************************************************)

(** Helper function for [sapply] which takes care of trivial cases. *)
Equations sapply_aux : subst -> qnat -> term :=
sapply_aux S_id i := E_tvar i ;
sapply_aux (S_cons t _) Q_zero := t ;
sapply_aux (S_ren r) i := E_tvar (rapply r i) ;
sapply_aux s i := E_subst (E_tvar i) s.

Lemma sapply_aux_sound e s i : 
  eeval e (sapply_aux s i) = seval e s (qeval e i).
Proof. funelim (sapply_aux s i) ; simp qeval eeval ; triv. Qed.
#[global] Hint Rewrite sapply_aux_sound : eeval seval.

Lemma sapply_aux_irred s i :
  sirred s -> qirred i ->
  (s <> S_id -> ~is_sren s -> ~(is_scons s /\ i = Q_zero) -> eirred (E_subst (E_tvar i) s)) ->
  eirred (sapply_aux s i).
Proof.
intros H1 H2 H3. funelim (sapply_aux s i).
all: try solve [ apply H3 ; triv ].
- now rewrite eirred_tvar.
- now apply sirred_cons in H1.
- rewrite eirred_tvar. apply rapply_rcomp_irred ; triv. 
  rewrite sirred_ren in H1. destruct r ; triv.
Qed.

(** Helper function for [rscomp], [srcomp], and [scomp]
    which takes care of trivial cases. *)
Equations scomp_aux : subst -> subst -> subst :=
scomp_aux s S_id := s ;
scomp_aux S_shift (S_cons t s) := s ;
scomp_aux s1 s2 := S_comp s1 s2.

Lemma scomp_aux_sound e s1 s2 : 
  seval e (scomp_aux s1 s2) =₁ O.scomp (seval e s1) (seval e s2).
Proof.
funelim (scomp_aux s1 s2) ; simp seval eeval ; triv.
now rewrite O.scomp_sid_r.
Qed.
#[global] Hint Rewrite scomp_aux_sound : seval eeval.

Lemma scomp_aux_irred s1 s2 :
  sirred s1 -> sirred s2 -> 
  (s2 <> S_id -> ~(s1 = S_shift /\ is_scons s2) -> sirred (S_comp s1 s2)) ->
  sirred (scomp_aux s1 s2).
Proof.
intros H1 H2 H3. funelim (scomp_aux s1 s2) ; triv.
all: try solve [ apply H3 ; triv ]. 
now rewrite sirred_cons in H2.
Qed.

(** Apply an irreducible substitution to an irreducible natural. *)
Equations sapply (s : subst) (i : qnat) : term by struct i :=
sapply s (Q_rapply r i) := sapply_aux (rscomp r s) i ;
sapply s i := sapply_aux s i

(** Compose an irreducible renaming with an irreducible substitution. *)
with rscomp (r : ren) (s : subst) : subst by struct r :=
rscomp R_id s := s ;
rscomp R_shift s := scomp_aux S_shift s ;
rscomp (R_cons i r) s := S_cons (sapply s i) (rscomp r s) ;
rscomp (R_comp r1 r2) s := rscomp r1 (rscomp r2 s) ;
rscomp (R_mvar m) s := scomp_aux (S_ren (R_mvar m)) s.

Lemma sapply_rscomp_sound e :
  (forall s i, eeval e (sapply s i) = seval e s (qeval e i)) *
  (forall r s, seval e (rscomp r s) =₁ O.rscomp (reval e r) (seval e s)).
Proof.
apply sapply_elim with 
  (P := fun s i res => eeval e res = seval e s (qeval e i))
  (P0 := fun r s res => seval e res =₁ O.rscomp (reval e r) (seval e s)).
all: intros ; simp eeval ; triv.
- rewrite H, H0. intros [|i'] ; reflexivity.
- rewrite H0, H. reflexivity.
Qed. 

Lemma sapply_sound e s i:
  eeval e (sapply s i) = seval e s (qeval e i).
Proof. now apply sapply_rscomp_sound. Qed.
#[global] Hint Rewrite sapply_sound : eeval seval.

Lemma rscomp_sound e r s :
  seval e (rscomp r s) =₁ O.rscomp (reval e r) (seval e s).
Proof. now apply sapply_rscomp_sound. Qed.
#[global] Hint Rewrite rscomp_sound : eeval seval.

Lemma sapply_rscomp_irred :
  (forall s i, sirred s -> qirred i -> eirred (sapply s i)) *
  (forall r s, rirred r -> sirred s -> sirred (rscomp r s)).
Proof.
apply sapply_elim with 
  (P := fun s i res => sirred s -> qirred i -> eirred res)
  (P0 := fun r s res => rirred r -> sirred s -> sirred res).
all: intros ; triv.
- apply sapply_aux_irred ; triv. intros H1 H2 H3. rewrite eirred_subst_var.
  split6 ; triv. intros [? ?] ; triv.
- rewrite qirred_rapply in H1. apply sapply_aux_irred ; triv. 
  + now apply H.
  + intros H2 H3 H4. rewrite eirred_subst_var. split6 ; triv.
    * now apply H.
    * intros [? ?] ; triv.
- apply sapply_aux_irred ; triv. intros H1 H2 H3. rewrite eirred_subst_var.
  split6 ; triv. 
- apply scomp_aux_irred ; triv. intros H1. rewrite sirred_shift_l.
  split3 ; triv. 
- rewrite sirred_cons. rewrite rirred_cons in H1. split.
  + apply H ; triv.
  + apply H0 ; triv.
- assert (H3 : rirred r1 /\ rirred r2).
  { split ; intros H' ; apply H1 ; triv. }
  apply H0 ; triv. apply H ; triv.
- apply scomp_aux_irred ; triv.
  + rewrite sirred_ren ; triv.
  + intros H1 H2. rewrite sirred_ren_l. split3 ; triv.
Qed.

(** Turn an irreducible renaming into an irreducible substitution. *)
Equations sren (r : ren) : subst :=
sren R_id := S_id ;
sren R_shift := S_shift ;
sren (R_cons i r) := S_cons (E_tvar i) (sren r) ;
sren (R_comp r1 r2) := S_comp (sren r1) (sren r2) ;
sren (R_mvar r) := S_ren (R_mvar r).

Lemma sren_sound e r : 
  seval e (sren r) =₁ O.rscomp (reval e r) O.E_var.
Proof.
funelim (sren r) ; simp eeval qeval ; triv.
+ rewrite H. intros [|] ; reflexivity.
+ rewrite H0, H. reflexivity.
Qed.  
#[global] Hint Rewrite sren_sound : seval eeval.

Lemma sren_irred r : rirred r -> sirred (sren r).
Proof.
intros H. funelim (sren r) ; triv.
- rewrite sirred_cons, eirred_tvar. rewrite rirred_cons in H0.
  split ; triv. now apply H.
- rewrite rirred_comp in H1. feed H ; triv. feed H0 ; triv.
  rewrite sirred_comp. split7 ; triv.
  + funelim (sren r1) ; try discriminate. triv.
  + funelim (sren r1) ; try discriminate. triv.
  + funelim (sren r1) ; try discriminate. triv.
  + funelim (sren r2) ; try discriminate. triv.
  + funelim (sren r1) ; triv. funelim (sren r2) ; triv.
    destruct H2 as (_ & _ & _ & _ & _ & _ & H2). triv.     
- rewrite sirred_ren. triv.
Qed.

(** Lift a renaming through a binder. *)
Equations rup (r : ren) : ren :=
rup r := R_cons Q_zero (rcomp r R_shift).

Lemma rup_sound e r : 
  reval e (rup r) =₁ O.up_ren (reval e r).
Proof. simp rup qeval. reflexivity. Qed.
#[global] Hint Rewrite rup_sound : reval qeval.

Lemma rup_irred r : rirred r -> rirred (rup r).
Proof. 
intros H. simp rup. rewrite rirred_cons. split ; triv.
apply rapply_rcomp_irred ; triv.
Qed.

(** Helper function for [ren] which takes care of trivial cases. *)
Equations rename_aux {k} (t : expr k) (r : ren) : expr k :=
rename_aux t R_id := t ;
rename_aux t r := E_ren t r.

Lemma rename_aux_sound e {k} (t : expr k) r :
  eeval e (rename_aux t r) = O.rename (eeval e t) (reval e r).
Proof.
funelim (rename_aux t r) ; simp reval ; triv. now rewrite O.ren_rid.
Qed.
#[global] Hint Rewrite rename_aux_sound : eeval seval.

Lemma rename_aux_irred {k} (t : expr k) r :
  eirred t -> rirred r -> (r <> R_id -> eirred (E_ren t r)) ->
  eirred (rename_aux t r).
Proof.
intros H1 H2 H3. funelim (rename_aux t r) ; triv.
all: solve [ apply H3 ; triv ].
Qed.

(** Helper function for [ren] which takes care of trivial cases. *)
Equations substitute_aux {k} (t : expr k) (s : subst) : expr k :=
substitute_aux t S_id := t ;
substitute_aux (E_tvar i) (S_ren r) := E_tvar (rapply r i) ;
substitute_aux t (S_ren r) := E_ren t r ;
substitute_aux (E_tvar Q_zero) (S_cons t _) := t ;
substitute_aux t s := E_subst t s.

Lemma substitute_aux_sound e {k} (t : expr k) s :
  eeval e (substitute_aux t s) = O.substitute (eeval e t) (seval e s).
Proof.
funelim (substitute_aux t s) ; simp seval eeval qeval ; triv.
all: try solve [ now rewrite O.ren_is_subst ].
now rewrite O.subst_sid.
Qed.
#[global] Hint Rewrite substitute_aux_sound : eeval seval.

Lemma substitute_aux_irred {k} (t : expr k) s :
  eirred t -> sirred s -> 
  (match s with S_ren r => ~is_tvar t -> eirred (E_ren t r) | _ => True end) ->
  (s <> S_id -> ~is_sren s -> ~(is_tvar_zero t /\ is_scons s) -> eirred (E_subst t s)) ->
  eirred (substitute_aux t s).
Proof.
intros H1 H2 H3 H4. funelim (substitute_aux t s) ; triv.
all: try solve [ apply H3 ; triv ].
all: try solve [ apply H4 ; triv ].
- now rewrite sirred_cons in H2.
- rewrite eirred_tvar in *. rewrite sirred_ren in H2. 
  destruct r ; try discriminate. apply rapply_rcomp_irred ; triv.
Qed.

(** Apply an irreducible renaming to an irreducible expression. *)
Equations rename {k} (t : expr k) (r : ren) : expr k by struct t :=
rename (E_tvar i) r := E_tvar (rapply r i) ;
rename (E_tctor c al) r := E_tctor c (rename al r) ;
rename E_al_nil _ := E_al_nil ;
rename (E_al_cons a al) r := E_al_cons (rename a r) (rename al r) ;
rename (E_abase b x) _ := E_abase b x ;
rename (E_aterm t) r := E_aterm (rename t r) ;
rename (E_abind a) r := E_abind (rename a (rup r)) ;
rename (E_ren e r1) r2 := rename_aux e (rcomp r1 r2) ;
rename (E_subst e s) r := substitute_aux e (srcomp s r) ;
rename e r := rename_aux e r 

(** Compose an irreducible substitution with an irreducible renaming. *)
with srcomp (s : subst) (r : ren) : subst by struct s :=
srcomp S_id r := sren r ;
srcomp (S_cons t s) r := S_cons (rename t r) (srcomp s r) ;
srcomp (S_comp s1 s2) r := scomp_aux s1 (srcomp s2 r) ;
srcomp s r := scomp_aux s (sren r). 

Lemma rename_srcomp_sound e : 
  (forall {k} (t : expr k) r, eeval e (rename t r) = O.rename (eeval e t) (reval e r)) *
  (forall s r, seval e (srcomp s r) =₁ O.srcomp (seval e s) (reval e r)).
Proof.
apply rename_elim with 
  (P := fun {k} (t : expr k) r res => eeval e res = O.rename (eeval e t) (reval e r))
  (P0 := fun s r res => seval e res =₁ O.srcomp (seval e s) (reval e r)).
all: intros ; simp eeval seval qeval reval ; triv.
- now rewrite H.
- now rewrite H, H0.
- now rewrite H.
- rewrite H. now rewrite rup_sound.
- now rewrite O.ren_ren.
- now rewrite O.ren_subst, H.
- rewrite H, H0. intros [|] ; reflexivity.
- rewrite H. intros i. cbv [O.scomp O.srcomp]. now rewrite O.ren_subst.
- intros i. cbv [O.scomp O.srcomp]. now rewrite O.ren_is_subst.
Qed.

Lemma rename_sound {k} e (t : expr k) r :
  eeval e (rename t r) = O.rename (eeval e t) (reval e r).
Proof. now apply rename_srcomp_sound. Qed.
#[global] Hint Rewrite @rename_sound : eeval seval.

Lemma srcomp_sound e s r :
  seval e (srcomp s r) =₁ O.srcomp (seval e s) (reval e r).
Proof. now apply rename_srcomp_sound. Qed.
#[global] Hint Rewrite srcomp_sound : eeval seval.

Lemma rename_srcomp_irred :
  (forall {k} (t : expr k) r, eirred t -> rirred r -> eirred (rename t r)) *
  (forall s r, sirred s -> rirred r -> sirred (srcomp s r)).
Proof.
apply rename_elim with 
  (P := fun {k} (t : expr k) r res => eirred t -> rirred r -> eirred res)
  (P0 := fun s r res => sirred s -> rirred r -> sirred res).
all: intros ; triv.
- rewrite eirred_tvar in *. apply rapply_rcomp_irred ; triv.
- rewrite eirred_tctor in *. now apply H.
- apply rename_aux_irred ; triv. intros H1. intros H' ; inv H' ; triv.
  destruct H4 ; triv.
- rewrite eirred_al_cons in *. split ; [apply H | apply H0] ; triv.
- rewrite eirred_aterm in *. now apply H.
- rewrite eirred_abind in *. apply H ; triv. now apply rup_irred.
- rewrite eirred_ren in H. apply rename_aux_irred ; triv.
  + destruct e ; triv.
  + apply rapply_rcomp_irred ; triv.
  + intros H2. rewrite eirred_ren. split3 ; triv.
    apply rapply_rcomp_irred ; triv.
- rewrite eirred_subst in H0. feed2 H ; triv. 
  apply substitute_aux_irred ; triv.
  + destruct (srcomp s r) ; triv. intros H4. rewrite sirred_ren in H. 
    destruct r0 ; try discriminate. rewrite eirred_ren. split3 ; triv.
    destruct H0 as (_ & _ & H0 & _). destruct e ; triv.
  + intros H4 H5 H6. rewrite eirred_subst. split7 ; triv.
- now apply sren_irred.
- apply scomp_aux_irred ; triv. 
  + now apply sren_irred.
  + intros H1 H2. rewrite sirred_shift_l. split3 ; triv.
    now apply sren_irred.
- rewrite sirred_cons in *. split ; [apply H | apply H0] ; triv.
- rewrite sirred_comp in H0. feed2 H ; triv. apply scomp_aux_irred ; triv.
  intros H4 H5. rewrite sirred_comp. split7 ; triv.
- rewrite sirred_ren in H. destruct r0 ; triv. apply scomp_aux_irred.
  + now rewrite sirred_ren.
  + now apply sren_irred.
  + intros H1 H2. rewrite sirred_ren_l. split3 ; triv. now apply sren_irred.
- apply scomp_aux_irred ; triv.
  + now apply sren_irred.
  + intros H1 H2. rewrite sirred_mvar_l. split ; triv.
    now apply sren_irred.   
Qed.



End Make.

(** Testing. *)

Inductive base := BString.
Definition denote_base (b : base) : Type := 
  match b with BString => string end.

Inductive ctor := CApp | CLam.
Definition ctor_type c : list (@arg_ty base) := 
  match c with 
  | CApp => [ AT_term ; AT_term ]
  | CLam => [ AT_base BString ; AT_bind AT_term ]
  end.

Module S.
Definition t := Build_signature base denote_base ctor ctor_type.
End S.

Module T := Make (S).
Import T.

Axiom n : nat.
Axiom m : nat.
Axiom r : O.ren.

Definition left := (O.rcons n r) (n + S m) + S n.
Definition right := n.

From Ltac2 Require Import Printf.

(** Turn a list of [constr] into a Rocq list. 
    [ty] is the type of each element in the list, which is needed
    to build the empty list. *)
Ltac2 rec coq_list (ty : constr) (xs : constr list) : constr :=
  match xs with 
  | [] => constr:(@nil $ty)
  | x :: xs =>
    let xs := coq_list ty xs in 
    constr:(@cons $ty $x $xs)
  end.

(** Turn the Ltac2 representation of the environment into the equivalent
    Rocq representation. *)
Ltac2 build_env (e : env) : constr :=
  let e1 := coq_list constr:(nat) (e.(qnat_mvars)) in 
  let e2 := coq_list constr:(O.ren) (e.(ren_mvars)) in 
  let e3 := coq_list constr:(O.expr Kt) (e.(term_mvars)) in 
  let e4 := coq_list constr:(O.subst) (e.(subst_mvars)) in 
  constr:(
    Build_env 
      (fun n => List.nth n $e1 0)
      (fun n => List.nth n $e2 O.rid)
      (fun n => List.nth n $e3 (O.E_var 0))
      (fun n => List.nth n $e4 O.sid)).

Ltac2 test_tac () : unit :=
  lazy_match! Control.goal () with 
  | @eq nat ?l ?r => 
    let (e, l') := reify_nat (empty_env ()) l in 
    printf "%t" l' ;
    let e := build_env e in
    printf "ENV %t" e ;
    change (qeval $e $l' = $r) ;
    rewrite <-(qsimp_sound $e $l')
  | _ => Control.throw_invalid_argument "not an equality on naturals"
  end.

Lemma test : left = right.
Proof.
unfold left, right.
ltac2:(test_tac ()).
cbv [qsimp qsimp_functional rsimp_functional qplus qplus_neutral rapply
     rapply_clause_3 rapply_clause_4].
cbv [qeval reval qeval_functional reval_functional 
     assign_ren assign_qnat nth].
Admitted.