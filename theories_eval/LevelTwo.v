From Prototype Require Import Prelude Sig LevelOne.

Module Make (S : Sig).
Module O := LevelOne.Make (S).

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
    We provide discriminator functions which handle this, as well as 
    tactics [inv_discriminator] and [solve_discriminators]. *)

Definition is_qrapply x := exists r y, x = Q_rapply r y.
Definition is_qmvar x := exists m, x = Q_mvar m.

Definition is_rcons r := exists i r', r = R_cons i r'.
Definition is_rcomp r := exists r1 r2 , r = R_comp r1 r2.
Definition is_rmvar r := exists m, r = R_mvar m.

Definition is_rid_l r := exists r2, r = R_comp R_id r2.
Definition is_rshift_l r := exists r2, r = R_comp R_shift r2.
Definition is_rcons_l r := exists i r' r2, r = R_comp (R_cons i r') r2.
Definition is_rcomp_l r := exists r1 r2 r3, r = R_comp (R_comp r1 r2) r3.
Definition is_rmvar_l r := exists m r2, r = R_comp (R_mvar m) r2.

Definition is_scons s := exists t s', s = S_cons t s'.
Definition is_scomp s := exists s1 s2 , s = S_comp s1 s2.
Definition is_smvar s := exists m, s = S_mvar m.
Definition is_sren s := exists r, s = S_ren r.

Definition is_scons_l s := exists t s' s2, s = S_comp (S_cons t s') s2.
Definition is_scomp_l s := exists s1 s2 s3, s = S_comp (S_comp s1 s2) s3.
Definition is_smvar_l s := exists m s2, s = S_comp (S_mvar m) s2.
Definition is_sren_l s := exists r s', s = S_comp (S_ren r) s'.

(** This tactic tries to solve the goal by inverting a hypothesis of
    the form [is_qsucc _], [is_rmvar _], ... which is inconsistent.

    It either closes the goal or does nothing. *)
Ltac inv_discriminators :=
  solve [
    let H' := fresh "H" in
    repeat match goal with 
    | [ H : is_qrapply _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_qmvar _ |- _ ] => destruct H as (? & H') ; inv H'

    | [ H : is_rcons _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_rcomp _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_rmvar _ |- _ ] => destruct H as (? & H') ; inv H'
    
    | [ H : is_rid_l _ |- _ ] => destruct H as (? & H') ; inv H'
    | [ H : is_rshift_l _ |- _ ] => destruct H as (? & H') ; inv H'
    | [ H : is_rcons_l _ |- _ ] => destruct H as (? & ? & ? & H') ; inv H'
    | [ H : is_rcomp_l _ |- _ ] => destruct H as (? & ? & ? & H') ; inv H'
    | [ H : is_rmvar_l _ |- _ ] => destruct H as (? & ? & H') ; inv H'

    | [ H : is_scons _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_scomp _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_smvar _ |- _ ] => destruct H as (? & H') ; inv H'
    | [ H : is_sren _ |- _ ] => destruct H as (? & H') ; inv H'

    | [ H : is_scons_l _ |- _ ] => destruct H as (? & ? & ? & H') ; inv H'
    | [ H : is_scomp_l _ |- _ ] => destruct H as (? & ? & ? & H') ; inv H'
    | [ H : is_smvar_l _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_sren_l _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    end 
  ].
#[global] Hint Extern 3 => inv_discriminators : core.

(** This tactic tries to solve trivial goals of the form 
    [is_qsucc (Q_succ _)], [is_rmvar (R_mvar _)], ...

    It either closes the goal or does nothing. *)
Ltac solve_discriminators :=
  solve [
    match goal with 
    | |- is_qrapply (Q_rapply _ _) => repeat eexists
    | |- is_qmvar (Q_mvar _) => repeat eexists

    | |- is_rcons (R_cons _ _)  => repeat eexists
    | |- is_rcomp (R_comp _ _)  => repeat eexists
    | |- is_rmvar (R_mvar _)  => repeat eexists

    | |- is_rid_l (R_comp R_id _) => repeat eexists
    | |- is_rshift_l (R_comp R_shift _) => repeat eexists
    | |- is_rcons_l (R_comp (R_cons _ _) _) => repeat eexists
    | |- is_rcomp_l (R_comp (R_comp _ _) _) => repeat eexists
    | |- is_rmvar_l (R_comp (R_mvar _) _) => repeat eexists

    | |- is_scons (S_cons _ _) => repeat eexists
    | |- is_scomp (S_comp _ _) => repeat eexists
    | |- is_smvar (S_mvar _) => repeat eexists
    | |- is_sren (S_ren _) => repeat eexists

    | |- is_scons_l (S_comp (S_cons _ _) _)  => repeat eexists
    | |- is_scomp_l (S_comp (S_comp _ _) _)  => repeat eexists
    | |- is_smvar_l (S_comp (S_mvar _) _)  => repeat eexists
    | |- is_sren_l (S_comp (S_ren) _) => repeat eexists
    end 
  ].
#[global] Hint Extern 3 => solve_discriminators : core.

(*********************************************************************************)
(** *** Irreducible forms for renamings & naturals. *)
(*********************************************************************************)

(** Reducible quoted naturals. *)
Inductive qred : qnat -> Prop :=

(** Congruence. *)
| QR_ren r x : rred r \/ qred x -> qred (Q_rapply r x)

| QR_ren_ren r1 r2 i : qred (Q_rapply r1 (Q_rapply r2 i))
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

Lemma qirred_ren_mvar m i : 
  qirred (Q_rapply (R_mvar m) i) <-> qirred i /\ ~is_qrapply i.
Proof.
split ; intros H.
- split ; intros H' ; apply H ; clear H.
  + constructor ; now right.
  + destruct H' as (r & i' & ->). now constructor. 
- intros H'. inv H'.
  + destruct H1 ; triv.
  + destruct H ; triv.
  + destruct H1 ; triv.
Qed.     

Lemma qirred_ren_cons i r k :
  qirred (Q_rapply (R_cons i r) k) <-> qirred i /\ rirred r /\ is_qmvar k.
Proof.
split.
- intros H. split3.
  + intros H' ; apply H ; clear H. constructor ; left. constructor ; now left.
  + intros H' ; apply H ; clear H. constructor ; left. constructor ; now right. 
  + destruct k ; triv. 
- intros (H1 & H2 & (? & ->)) H. inv H ; triv.
  destruct H3 ; triv. inv H0. destruct H4 ; triv.
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
- intros H. split4 ; triv.
  + intros H' ; apply H ; triv.
  + intros -> ; apply H. triv.
- intros (H1 & H2) H. inv H ; triv.
  + destruct H3 ; triv.
  + destruct H3 ; triv.
Qed.

(*Lemma rirred_comp r1 r2 : 
  rirred (R_comp r1 r2) <-> 
    rirred r1 /\ rirred r2 /\ r2 <> R_id /\ (r1 = R_shift \/ is_rmvar r1).
Proof.
split.
- intros H. split4.
  + intros H' ; apply H. triv.
  + intros H' ; apply H. triv.
  + intros ->. triv.
  + destruct r1 ; triv.
- intros (H1 & H2 & H3 & [-> | (? & ->)]).
  + rewrite rirred_shift_l. split4 ; triv.  *)

(*********************************************************************************)
(** *** Simplification of renamings & quoted naturals. *)
(*********************************************************************************)

(*(** Helper function for [rdrop] which takes care of 
    removing left composition by the identity. *)
Equations do_rshift : qnat -> ren -> ren :=
do_rshift Q_zero r := r ;
do_rshift k r := R_comp (R_shift k) r.

Lemma do_rshift_sound e k r : 
  reval e (do_rshift k r) =₁ O.rcomp (O.rshift (qeval e k)) (reval e r).
Proof. funelim (do_rshift k r) ; triv. Qed.
#[global] Hint Rewrite do_rshift_sound : reval.

Lemma do_rshift_irred k r :
  qirred k -> rirred r -> (k <> Q_zero -> rirred (R_comp (R_shift k) r)) -> rirred (do_rshift k r).
Proof. intros H1 H2 H3. funelim (do_rshift k r) ; triv ; now apply H3. Qed.*)

(** Drop the first element in an irreducible renaming. *)
Equations rtail (r : ren) : ren by struct r :=
rtail R_id := R_shift ;
rtail (R_cons _ r) := r ;
rtail r := R_comp R_shift r.

Lemma rtail_sound e r : 
  reval e (rtail r) =₁ O.rcomp O.rshift (reval e r).
Proof. funelim (rtail r) ; simp qeval ; triv. Qed.  
#[global] Hint Rewrite rtail_sound : qeval reval.

Lemma rtail_irred r : rirred r -> rirred (rtail r).
Proof.
intros H. funelim (rtail r) ; triv.
- rewrite rirred_shift_l. split4 ; triv.
- now rewrite rirred_cons in H.
- rewrite rirred_shift_l. split4 ; triv.
  intros (? & ? & ? & H1). inv H1. triv.
- rewrite rirred_shift_l. split4 ; triv.
Qed. 

(** Apply an irreducible renaming to an irreducible quoted natural. *)
Equations rapply (r : ren) (i : qnat) : qnat by struct r := 
rapply R_id i := i ;
rapply R_shift 
rapply (R_shift k) i := qplus k i ;
rapply (R_mvar m) r := Q_rapply (R_mvar m) r ;
rapply (R_cons i1 r) i with i => {
  | Q_zero := i1
  | Q_succ i' := rapply r i'
  | _ := Q_rapply (R_cons i1 r) i } ;
rapply (R_comp r1 r2) i with r1 => {
  | R_shift k := rapply r2 (qplus k i) ;
  | R_mvar m := rapply r2 (Q_rapply (R_mvar m) i)
  | _ => (* This should not happen. *) Q_rapply (R_comp r1 r2) i }.

Lemma rapply_sound e r i : 
  qeval e (rapply r i) = reval e r (qeval e i).
Proof.
funelim (rapply r i) ; simp qeval ; triv.
rewrite H. simp qeval. reflexivity.
Qed.
#[global] Hint Rewrite rapply_sound : qeval.

Lemma rapply_irred r i : 
  rirred r -> qirred i -> qirred (rapply r i).
Proof. 
intros H1 H2. funelim (rapply r i) ; triv.
- rewrite rirred_shift in H1. now apply qplus_irred.
- now rewrite qirred_ren_mvar.
- now rewrite rirred_cons in H1.
- rewrite rirred_cons in H1. rewrite qirred_succ in H2. now apply H.
- rewrite qirred_ren_cons. rewrite rirred_cons in H1. split5 ; triv.
- rewrite qirred_ren_cons. rewrite rirred_cons in H1. split5 ; triv.
- rewrite qirred_ren_cons. rewrite rirred_cons in H1. split5 ; triv.
- rewrite rirred_shift_l in H1. apply H ; triv. now apply qplus_irred.
- rewrite rirred_mvar_l in H1. apply H ; triv. now rewrite qirred_ren_mvar.
Qed.   

(** Helper function for [rcomp] which takes care of 
    removing [rid] in the right hand side.*)
Equations rcomp_aux : ren -> ren -> ren :=
rcomp_aux r rid := r ;
rcomp_aux r1 r2 := R_comp r1 r2. 

Lemma rcomp_aux_sound e r1 r2 : 
  reval e (rcomp_aux r1 r2) =₁ O.rcomp (reval e r1) (reval e r2).
Proof. funelim (rcomp_aux r1 r2) ; simp qeval ; triv. Qed.
#[global] Hint Rewrite rcomp_aux_sound : qeval reval. 

Lemma rcomp_aux_irred r1 r2 :
  rirred r1 -> rirred r2 -> (r2 <> rid -> rirred (R_comp r1 r2)) -> rirred (rcomp_aux r1 r2).
Proof. 
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; triv.
all: apply H3 ; intros H ; inv H.
Qed.  

(** Compose two irreducible renamings. *)
Equations rcomp (r1 r2 : ren) : ren by struct r1 :=
rcomp (R_shift k) r := rdrop k r ;
rcomp (R_cons i r1) r2 := R_cons (rapply r2 i) (rcomp r1 r2) ;
rcomp (R_comp r1 r2) r3 with r1 => {
  | R_mvar m => rcomp_aux (R_mvar m) (rcomp r2 r3) ;
  | R_shift k => rdrop k (rcomp r2 r3) 
  | _ => (* This should not happen. *) R_comp (R_comp r1 r2) r3 } ;
rcomp (R_mvar m) r := rcomp_aux (R_mvar m) r.

Lemma rcomp_sound e r1 r2 : 
  reval e (rcomp r1 r2) =₁ O.rcomp (reval e r1) (reval e r2).
Proof.
funelim (rcomp r1 r2) ; simp reval qeval ; triv.
- rewrite H. now rewrite O.rcomp_rcons_distrib.
- rewrite H. now rewrite O.rcomp_assoc.
- rewrite H. now rewrite O.rcomp_assoc.
Qed.  
#[global] Hint Rewrite rcomp_sound : reval qeval.

Lemma rcomp_irred r1 r2 : 
  rirred r1 -> rirred r2 -> rirred (rcomp r1 r2).
Proof.
intros H1 H2. funelim (rcomp r1 r2) ; triv.
- rewrite rirred_shift in H1. now apply rdrop_irred.
- rewrite rirred_cons in * ; split.
  + now apply rapply_irred.
  + now apply H.
- apply rcomp_aux_irred ; triv. intros H. now rewrite rirred_mvar_l.
- rewrite rirred_shift_l in H1. apply rdrop_irred ; triv. now apply H.
- rewrite rirred_mvar_l in H1. apply rcomp_aux_irred ; triv.  
  + now apply H.
  + intros H3. rewrite rirred_mvar_l. split ; triv. apply H ; triv.
Qed.

(** Simplify a quoted natural. *)
Equations qsimp : qnat -> qnat :=
qsimp Q_zero := Q_zero ;
qsimp (Q_succ i) := Q_succ (qsimp i) ;
qsimp (Q_plus x y) := qplus (qsimp x) (qsimp y) ;
qsimp (Q_rapply r i) := rapply (rsimp r) (qsimp i) ;
qsimp (Q_mvar m) := Q_mvar m 

(** Simplify a renaming. *)
with rsimp : ren -> ren :=
rsimp (R_shift k) := R_shift (qsimp k) ;
rsimp (R_cons i r) := R_cons (qsimp i) (rsimp r) ;
rsimp (R_comp r1 r2) := rcomp (rsimp r1) (rsimp r2) ;
rsimp (R_mvar m) := R_mvar m.

Lemma qrsimp_sound_aux e :
  (forall i, qeval e (qsimp i) = qeval e i) *
  (forall r, reval e (rsimp r) =₁ reval e r).
Proof. 
apply qsimp_elim with 
  (P := fun i res => qeval e res = qeval e i)
  (P0 := fun r res => reval e res =₁ reval e r).
all: intros ; simp qeval reval ; triv.
- now rewrite H, H0.
- now rewrite H.
- now rewrite H, H0.
- now rewrite H, H0.
Qed.    

Lemma qsimp_sound e i : qeval e (qsimp i) = qeval e i.
Proof. now apply qrsimp_sound_aux. Qed.
#[global] Hint Rewrite qsimp_sound : qeval.

Lemma rsimp_sound e r : reval e (rsimp r) =₁ reval e r.
Proof. now apply qrsimp_sound_aux. Qed.
#[global] Hint Rewrite rsimp_sound : qeval reval.

Lemma qrsimp_irred_aux : 
  (forall i, qirred (qsimp i)) * (forall r, rirred (rsimp r)).
Proof.
apply qsimp_elim with (P := fun _ res => qirred res) (P0 := fun _ res => rirred res).
all: intros ; triv.
- now rewrite qirred_succ.
- now apply qplus_irred.
- now apply rapply_irred.
- now rewrite rirred_shift.
- now rewrite rirred_cons.
- now apply rcomp_irred.
Qed.

Lemma qsimp_irred i : qirred (qsimp i).
Proof. now apply qrsimp_irred_aux. Qed.

Lemma rsimp_irred r : rirred (rsimp r).
Proof. now apply qrsimp_irred_aux. Qed.
  
(*********************************************************************************)
(** *** Irreducible forms for substitutions & expressions. *)
(*********************************************************************************)

(** Expressions in which we can push renamings/substitutions. *)
Definition is_epush {k} (e : expr k) : Prop :=
  match e with 
  | E_mvar _ | E_tvar _ => False  
  | _ => True 
  end.

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
| ER_push_ren {k} r (e : expr k) : is_epush e -> ered (E_ren e r)
| ER_push_subst {k} s (e : expr k) : is_epush e -> ered (E_subst e s)
| ER_ren_var r i : ered (E_ren (E_tvar i) r)

(** Apply a substitution to a variable. *)
| ER_sshift_var i s : 
    is_sshift s \/ is_sshift_l s -> ered (E_subst (E_tvar i) s)
| ER_scons_zero s : 
    is_scons s \/ is_scons_l s -> ered (E_subst (E_tvar Q_zero) s)
| ER_scons_succ s i : 
   is_scons s \/ is_scons_l s -> ered (E_subst (E_tvar (Q_succ i)) s)
| ER_sren_var s i : 
   is_sren s \/ is_sren_l s -> ered (E_subst (E_tvar i) s)

(** Apply a substitution/renaming to a meta-variable. *)
| ER_ren_rid (m : mvar) : ered (E_ren (E_mvar m) rid)
| ER_subst_sid (m : mvar ) : ered (E_subst (E_mvar m) sid)
| ER_ren_mvar (m : mvar) r : ered (E_subst (E_mvar m) (S_ren r))

(** Reducible substitutions. *)
with sred : subst -> Prop :=

(** Congruence. *)
| SR_shift k : qred k -> sred (S_shift k) 
| SR_cons t s : ered t \/ sred s -> sred (S_cons t s)
| SR_comp s1 s2 : sred s1 \/ sred s2 -> sred (S_comp s1 s2)
| SR_ren r : rred r -> sred (S_ren r)

(** Composition should be right associated, with neutral element [sid]. *)
| SR_sid_l s : sred (S_comp sid s)
| SR_sid_r s : sred (S_comp s sid)
| SR_comp_l s1 s2 s3: sred (S_comp (S_comp s1 s2) s3)

(** Push [S_ren] into renamings. *)
| SR_ren_distrib r : ~is_rmvar r -> sred (S_ren r)
(** Composition distributes over [S_cons]. *)
| SR_cons_l t s1 s2 : sred (S_comp (S_cons t s1) s2)
(** Combine successive shifts. *)
| SR_shift_l k s : 
  is_sshift s \/ is_sshift_l s -> sred (S_comp (S_shift k) s)
(** Simplify [shift >> (t . s)] into [s]. *)
| SR_shift_cons k s : 
  is_scons s \/ is_scons_l s -> sred (S_comp (S_shift (Q_succ k)) s).

Hint Constructors ered : core.
Hint Constructors sred : core.

(** Irreducible expression. *)
Definition eirred {k} (e : expr k) := ~ered e.

(** Irreducible substitution. *)
Definition sirred s := ~sred s.

(*********************************************************************************)
(** *** Properties of substitution & expression irreducible forms. *)
(*********************************************************************************)

Lemma sirred_shift k : sirred (S_shift k) <-> qirred k.
Proof.
split ; intros H H' ; apply H ; clear H.
- now constructor.
- now inv H'.
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

Lemma sirred_shift_l k s : 
  sirred (S_comp (S_shift k) s) <->
    qirred k /\ 
    sirred s /\ 
    k <> Q_zero /\
    ~is_sshift s /\ 
    ~is_sshift_l s /\
    ~(is_qsucc k /\ is_scons s).
Proof.
split.
- intros H. split6 ; intros H' ; apply H ; clear H.
  + constructor. left. now constructor.
  + constructor. now right.
  + subst. now constructor.
  + destruct H' as [k' ->]. apply SR_shift_l. triv.
  + destruct H' as (k' & r' & ->). apply SR_shift_l ; triv. 
  + destruct H' as [(k' & ->) (i & r' & ->)]. apply SR_shift_cons. left. triv.
- intros (H1 & H2 & H3) H. inv H ; try easy.
  + destruct H4 ; auto. now inv H0.
  + destruct H3 as (_ & H3 & _) ; apply H3. triv.
  + destruct H3 as (_ & H3 & H3' & _) ; apply H3. now destruct H4.
  + destruct H3 as (_ & _ & _ & H3) ; apply H3.
Admitted.

(*Lemma sirred_ren_l r s : 
  sirred (S_comp (S_ren r) s) <-> is_rmvar r /\ sirred s /\ s <> sid.
Proof.
split ; intros H.
- split3.
  + apply Decidable.not_not.
    * unfold Decidable.decidable. destruct r ; triv.
    * intros H'. apply H ; clear H. now apply SR_ren_l.
  + intros H' ; apply H ; clear H. constructor. now right.
  + intros H'. apply H ; clear H. subst. now constructor.
- intros H'. inv H' ; triv. destruct H1 ; triv. inv H0.
  destruct H as ((m & ->) & _ & _). inv H2.
Qed.

Lemma sirred_mvar_l m s : 
  sirred (S_comp (S_mvar m) s) <-> sirred s /\ s <> sid.
Proof.
split.
- intros H. split.
  + intros H'. apply H ; clear H. apply SR_comp. now right.
  + intros H' ; subst. apply H. now constructor. 
- intros (H & H') H''. inv H'' ; triv. now destruct H1.
Qed. 

Lemma sirred_ren r : sirred (S_ren r) <-> rirred r.
Proof.
split ; intros H H' ; apply H ; clear H.
- now constructor.
- now inv H'.
Qed.  *)

(*********************************************************************************)
(** *** Simplify substitutions & expressions. *)
(*********************************************************************************)

(** Helper function for [sdrop] which takes care of 
    removing left composition by the identity. *)
Equations do_sshift : qnat -> subst -> subst :=
do_sshift Q_zero s := s ;
do_sshift k s := S_comp (S_shift k) s.

Lemma do_sshift_sound e k s : 
  seval e (do_sshift k s) =₁ O.scomp (O.sshift (qeval e k)) (seval e s).
Proof. funelim (do_sshift k s) ; triv. Qed.
#[global] Hint Rewrite do_sshift_sound : seval.

Lemma do_sshift_irred k s :
  qirred k -> sirred s -> (k <> Q_zero -> sirred (S_comp (S_shift k) s)) -> sirred (do_sshift k s).
Proof. intros H1 H2 H3. funelim (do_sshift k s) ; triv ; now apply H3. Qed.

(** Drop the [k] first elements in an irreducible substitution [s]. *)
Equations sdrop (k : qnat) (s : subst) : subst by struct s :=
sdrop k (S_shift k') := S_shift (qplus k k') ;
sdrop k (S_cons t s) with k := {
  | Q_succ k' => sdrop k' s ;
  | _ => do_sshift k (S_cons t s) } ;
sdrop k (S_comp (S_shift k') s) := sdrop (qplus k k') s ;
sdrop k (S_ren r) := S_ren (rdrop k r) ;
sdrop k s := do_sshift k s.

Lemma sdrop_sound e k s : 
  seval e (sdrop k s) =₁ O.scomp (O.sshift (qeval e k)) (seval e s).
Proof.
funelim (sdrop k s) ; simp seval eeval qeval ; triv.
- now rewrite O.sshift_plus.
- rewrite H. simp qeval. now rewrite <-O.scomp_assoc, O.sshift_plus.
Qed.
#[global] Hint Rewrite sdrop_sound : seval eeval.   

Lemma sdrop_irred k s :
  qirred k -> sirred s -> sirred (sdrop k s).
Proof.
intros H1 H2. funelim (sdrop k s) ; triv.
all: try solve [ apply do_sshift_irred ; triv ; [] ; intros H3 ; rewrite sirred_shift_l ;
  split6 ; triv ; [] ; intros (? & ?) ; triv ].
- rewrite sirred_shift in *. now apply qplus_irred.
- rewrite sirred_shift_l in H2. apply H ; triv. now apply qplus_irred.
- rewrite sirred_ren in *. now apply rdrop_irred.
- rewrite qirred_succ in H1. rewrite sirred_cons in H2. now apply H.
Qed.

(** Apply an irreducible substitution to an irreducible natural. *)
Equations sapply (s : subst) (i : qnat) : term by struct s := 
sapply (S_shift k) i := E_tvar (qplus k i) ;
sapply (S_comp (S_shift k) s) i := sapply s (qplus k i) ;

sapply (S_cons t s) Q_zero := t ;
sapply (S_comp (S_cons t s1) s2) Q_zero := t ;

sapply (S_cons t s) (Q_succ i) := sapply s i ;
sapply (S_comp (S_cons t s1) s2) (Q_succ i) := sapply s2 (sapply s1 i) ;

sapply (S_ren r) i := E_tvar (rapply r i) ;
sapply (S_comp (S_ren r) s) i := sapply s (rapply r i) ;

sapply s i with i := { 
  | Q_rapply (R_cons i0 r0) i' => E_subst (S_cons (sapply s i0) (rscomp r0 s)) i'
  | _ => E_subst (E_tvar i) s }.

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