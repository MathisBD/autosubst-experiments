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
| Q_zero : qnat 
| Q_succ : qnat -> qnat
| Q_plus : qnat -> qnat -> qnat 
| Q_ren : ren -> qnat -> qnat 
| Q_mvar : mvar -> qnat

(** Explicit renaming. *)
with ren :=
| R_shift : qnat -> ren
| R_cons : qnat -> ren -> ren
| R_comp : ren -> ren -> ren 
| R_mvar : mvar -> ren.

Notation "'Q_one'" := (Q_succ Q_zero).

(*********************************************************************************)
(** *** Expressions and explicit substitutions. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Expressions over an abstract signature. 
    Expressions are indexed by a kind: this is to avoid having too many 
    distinct constructors for instantiation. *)
Inductive expr : kind -> Type :=

(** Variable term constructor (de Bruijn index). *)
| E_tvar : qnat -> term
(** Non-variable term constructor, applied to a list of arguments. *)
| E_tctor : forall c, args (ctor_type S.t c) -> term

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
(** Term metavariable. We don't need argument or argument-list metavariables. *)
| E_mvar : mvar -> term

with subst :=
(** Shift substitution. *)
| S_shift : qnat -> subst
(** Substitution expansion. *)
| S_cons : term -> subst -> subst
(** Substitution composition. *)
| S_comp : subst -> subst -> subst
(** View a renaming as a substitution. *)
| S_ren : ren -> subst
(** Substitution metavariable. *)
| S_mvar : mvar -> subst

where "'term'" := (expr Kt)
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

(** Notations for common expressions. *)

(*Notation "'↑ᵣ' k" := (R_shift k) (at level 0, k at level 0).
Notation "i '.ᵣ' r" := (R_cons i r) (at level 60, right associativity).
Notation "r1 '>>ᵣ' r2" := (R_comp r1 r2) (at level 50, left associativity).

Notation "'↑ₛ' k" := (E_sshift k) (at level 0, k at level 0).
Notation "t '.ₛ' s" := (E_scons t s) (at level 60, right associativity).
Notation "s1 '>>ₛ' s2" := (E_scomp s1 s2) (at level 50, left associativity).

Notation "t '[ᵣ' s ']'" := (E_rinst t s) (at level 15, s at level 0, no associativity).
Notation "t '[ₛ' s ']'" := (E_sinst t s) (at level 15, s at level 0, no associativity).*)

(** The identity renaming. *)
Notation "'rid'" := (R_shift Q_zero).

(** The identity substitution. *)
Notation "'sid'" := (S_shift Q_zero).

(** Lift a renaming through a binder. *)
(*Definition up_ren (r : ren) : ren :=
  R_cons Q_zero (R_comp r (R_shift Q_one)).

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  S_cons (E_tvar Q_zero) (S_comp s (S_shift Q_one)).*)

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
  qeval (Q_succ i) := S (qeval i) ;
  qeval (Q_plus x y) := qeval x + qeval y ;
  qeval (Q_ren r i) := reval r (qeval i) ;
  qeval (Q_mvar x) := e.(assign_qnat) x
  
  with reval : ren -> O.ren :=
  reval (R_shift i) := O.rshift (qeval i) ;
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
  seval (S_shift k) := O.sshift (qeval k) ;
  seval (S_cons t s) := O.scons (eeval t) (seval s) ;
  seval (S_comp s1 s2) := O.scomp (seval s1) (seval s2) ;
  seval (S_ren r) := O.rscomp (reval r) O.E_var ;
  seval (S_mvar x) := e.(assign_subst) x.

End Evaluation.
 
(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

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

Ltac2 rec reify_nat (e : env) (t : constr) : env * constr := 
  lazy_match! t with 
  | 0 => e, constr:(Q_zero)
  | S ?i =>
    let (e, i) := reify_nat e i in 
    e, constr:(Q_succ $i)
  | ?x + ?y => 
    let (e, x) := reify_nat e x in 
    let (e, y) := reify_nat e y in 
    e, constr:(Q_plus $x $y)
  | ?r ?i =>
    let (e, r) := reify_ren e r in
    let (e, i) := reify_nat e i in
    e, constr:(Q_ren $r $i)
  | ?i => 
    let idx := nat_of_int (List.length (e.(qnat_mvars))) in
    let e := add_qnat_mvar i e in
    e, constr:(Q_mvar $idx)
  end

with reify_ren (e : env) (t : constr) : env * constr :=
  lazy_match! t with 
  | O.rshift ?k =>
    let (e, k) := reify_nat e k in 
    e, constr:(R_shift $k) 
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
  | O.sid => e, constr:(sid)
  | O.sshift ?k => 
    let (e, k) := reify_nat e k in 
    e, constr:(S_shift $k)
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
(** *** Normal forms. *)
(*********************************************************************************)

(** Reducible quoted natural. *)
Inductive qred : qnat -> Prop :=
(** Congruence. *)
| QR_succ x : qred x -> qred (Q_succ x)
| QR_plus x y : qred x \/ qred y -> qred (Q_plus x y)
| QR_ren r x : rred r \/ qred x -> qred (Q_ren r x)

(** Addition should pull out [Q_succ] from both arguments,
    and by right associated. *)
| QR_plus_zero_l x : qred (Q_plus x Q_zero)
| QR_plus_zero_r x : qred (Q_plus Q_zero x)
| QR_plus_plus_l x y z : qred (Q_plus (Q_plus x y) z)
| QR_plus_succ_l x y : qred (Q_plus (Q_succ x) y)
| QR_plus_succ_r x y : qred (Q_plus x (Q_succ y))

(* Renaming should be fully applied to their argument.  *)
| QR_ren_comp r1 r2 i : qred (Q_ren (R_comp r1 r2) i)
| QR_ren_shift k i : qred (Q_ren (R_shift k) i)
| QR_rcons_zero i r : qred (Q_ren (R_cons i r) Q_zero)
| QR_rcons_succ i r k : qred (Q_ren (R_cons i r) (Q_succ k))

(** Reducible renaming. *)
with rred : ren -> Prop :=
(** Congruence. *)
| RR_shift k : qred k -> rred (R_shift k)
| RR_cons i r : qred i \/ rred r -> rred (R_cons i r)
| RR_comp r1 r2 : rred r1 \/ rred r2 -> rred (R_comp r1 r2)

(** Composition should be right associated. *)
| RR_rid_l r : rred (R_comp rid r)
| RR_rid_r r : rred (R_comp r rid)
| RR_comp_l r1 r2 r3 : rred (R_comp (R_comp r1 r2) r3)

(** Renaming simplification. *)
| RR_cons_l i r1 r2 : rred (R_comp (R_cons i r1) r2)
| RR_shift_1 k1 k2 : rred (R_comp (R_shift k1) (R_shift k2))
| RR_shift_2 k1 k2 r : rred (R_comp (R_shift k1) (R_comp (R_shift k2) r))
| RR_shift_cons k i r : rred (R_comp (R_shift (Q_succ k)) (R_cons i r)).

Hint Constructors qred : core.
Hint Constructors rred : core.

(** Normal form quoted natural. *)
Definition qnorm x := ~ qred x.

(** Normal form renaming. *)
Definition rnorm r := ~ rred r.

(*********************************************************************************)
(** *** Normal form properties. *)
(*********************************************************************************)

Definition is_qsucc x := exists x', x = Q_succ x'.
Definition is_qplus x := exists y z, x = Q_plus y z.
Definition is_qren x := exists r y, x = Q_ren r y.

Definition is_rshift r := exists k, r = R_shift k.
Definition is_rcons r := exists i r', r = R_cons i r'.
Definition is_rcomp r := exists r1 r2 , r = R_comp r1 r2.
Definition is_rshift_l r := exists k r', r = R_comp (R_shift k) r'.

(** This tactic tries to solve the goal by inverting a hypothesis of
    the form [is_qsucc _], [is_qplus _], ... which is inconsistent.

    It either closes the goal or does nothing. *)
Ltac inv_is_ren_qnat :=
  solve [
    let H' := fresh "H" in
    match goal with 
    | [ H : is_qsucc _ |- _ ] => destruct H as (? & H') ; inv H'
    | [ H : is_qren _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_rshift _ |- _ ] => destruct H as (? & H') ; inv H'
    | [ H : is_rcons _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_rshift_l _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    | [ H : is_rcomp _ |- _ ] => destruct H as (? & ? & H') ; inv H'
    end ].
#[global] Hint Extern 2 => inv_is_ren_qnat : core.

Lemma qnorm_succ x :
  qnorm (Q_succ x) <-> qnorm x.
Proof.
split ; intros H H' ; apply H ; clear H.
- now constructor.
- now inv H'.
Qed.

Lemma qnorm_plus x y : 
  qnorm (Q_plus x y) <-> 
    qnorm x /\ qnorm y /\
    x <> Q_zero /\ y <> Q_zero /\
    ~is_qsucc x /\ ~is_qsucc y /\
    ~is_qplus x.
Proof.
split.
- intros H. split7 ; intros H' ; apply H ; clear H ; triv.
  + subst. now constructor.
  + subst. now constructor.
  + destruct H' as (x' & ->). now constructor.
  + destruct H' as (y' & ->). now constructor.
  + destruct H' as (x1 & x2 & ->). now constructor.
- intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) H. inv H ; triv.
  + destruct H8 ; auto.
  + apply H7. eexists ; eauto.
  + apply H5. eexists ; eauto.
  + apply H6. eexists ; eauto.
Qed.

Lemma qnorm_ren_mvar m i : 
  qnorm (Q_ren (R_mvar m) i) <-> qnorm i.
Proof.
split.
- intros H H'. apply H ; clear H. constructor. now right.
- intros H H'. inv H'. destruct H1 ; triv.
Qed.     

Lemma qnorm_ren_cons i r k :
  qnorm (Q_ren (R_cons i r) k) <->
    qnorm i /\ rnorm r /\ qnorm k /\ k <> Q_zero /\ ~is_qsucc k.
Proof.
split.
- intros H. split5 ; intros H' ; apply H ; clear H.
  + constructor ; left. constructor ; now left.  
  + constructor ; left. constructor ; now right. 
  + constructor ; now right.
  + subst. now constructor.
  + destruct H' as [k' ->]. now constructor.
- intros (H1 & H2 & H3 & H4 & H5) H. inv H ; triv.
  + destruct H6 ; triv. inv H0. destruct H7 ; triv.
  + apply H5. eexists ; eauto.
Qed.

(*Lemma qnorm_ren r i :
  qnorm (Q_ren r i) <-> 
    rnorm r /\ qnorm i /\ ~is_rshift r /\ ~is_rcomp r /\
    (is_rcons r -> i <> Q_zero /\ ~is_qsucc i).
Proof.
split.
- intros H. split5.
  + intros H' ; apply H ; clear H. apply QR_ren. now left.
  + intros H' ; apply H ; clear H. apply QR_ren. now right.
  + intros H' ; apply H ; clear H. destruct H' as (k & ->). now constructor.
  + intros H' ; apply H ; clear H. destruct H' as (? & ? & ->). now constructor.
  + intros (? & ? & ->). split ; intros H'' ; apply H ; clear H.
    * subst. now constructor.
    * destruct H'' as (? & H''). subst. now constructor.      
- intros (H1 & H2 & H3 & H4 & H5) H. inv H.
  + destruct H6 ; triv.
  + apply H4. eexists ; eauto.
  + apply H3. eexists ; eauto.
  + enough (Q_zero <> Q_zero) by auto. apply H5. eexists ; eauto.
  + enough (~is_qsucc (Q_succ k)).
    { apply H0. eexists ; eauto. }
    apply H5. eexists ; eauto.
Qed.
Admitted.*)

Lemma rnorm_shift k : 
  rnorm (R_shift k) <-> qnorm k.
Proof. 
split ; intros H H' ; apply H ; clear H.
- now constructor.
- now inv H'.
Qed.

Lemma rnorm_cons i r : 
  rnorm (R_cons i r) <-> qnorm i /\ rnorm r.
Proof.
split.
- intros H. split ; intros H' ; apply H.
  all: constructor ; auto.
- intros [H1 H2] H. inv H. destruct H3 ; auto.
Qed.

Lemma rnorm_mvar_l m r : 
  rnorm (R_comp (R_mvar m) r) <-> rnorm r /\ r <> rid.
Proof.
split.
- intros H. split.
  + intros H'. apply H ; clear H. apply RR_comp. now right.
  + intros H' ; subst. apply H. now constructor. 
- intros (H & H') H''. inv H''.
  + destruct H1 ; easy.
  + easy.
Qed.      

Lemma rnorm_shift_l k r : 
  rnorm (R_comp (R_shift k) r) <-> 
    qnorm k /\ 
    rnorm r /\ 
    k <> Q_zero /\ 
    ~is_rshift r /\ 
    ~is_rshift_l r /\
    ~(is_qsucc k /\ is_rcons r).
Proof.
split.
- intros H. split6 ; intros H' ; apply H ; clear H.
  + constructor. left. now constructor.
  + constructor. now right.
  + subst. now constructor.
  + destruct H' as [k' ->]. now constructor.
  + destruct H' as (k' & r' & ->). now constructor. 
  + destruct H' as [(k' & ->) (i & r' & ->)]. now constructor.   
- intros (H1 & H2 & H3) H. inv H ; try easy.
  + destruct H4 ; auto. now inv H0.
  + destruct H3 as (_ & H3 & _) ; apply H3. eexists ; eauto.
  + destruct H3 as (_ & H3 & _) ; apply H3. eexists ; eauto.
  + destruct H3 as (_ & _ & H3 & _) ; apply H3. eexists ; eauto. 
  + destruct H3 as (_ & _ & H3) ; apply H3. split ; eexists ; eauto.
Qed. 

(*********************************************************************************)
(** *** Normalization. *)
(*********************************************************************************)

(*(** We define the size of expressions, which is used to prove 
    termination of some simplification functions by well founded induction. *)

(** Size of a quoted natural. *)
Equations qsize : qnat -> nat :=
qsize Q_zero := 0 ;
qsize (Q_succ x) := S (qsize x) ;
qsize (Q_plus x y) := S (qsize x + qsize y) ;
qsize (Q_ren r x) := S (rsize r + qsize x) ;
qsize (Q_mvar _) := 0

(** Size of a renaming. *)
with rsize : ren -> nat :=
rsize (R_shift k) := S (qsize k) ;
rsize (R_cons i r) := S (qsize i + rsize r) ;
rsize (R_comp r1 r2) := S (rsize r1 + rsize r2) ;
rsize (R_mvar _) := 0.*)

(** Add two normal form quoted naturals, where the left hand side
    is neutral (i.e. is not Q_zero, Q_succ or Q_plus). *)
Equations qplus_neutral : qnat -> qnat -> qnat :=
qplus_neutral n Q_zero := n ;
qplus_neutral n (Q_succ x) := Q_succ (qplus_neutral n x) ;
qplus_neutral n x := Q_plus n x.

(*Lemma qsize_qplus_neutral x y : 
  qsize (qplus_neutral x y) <= S (qsize x + qsize y).
Proof. funelim (qplus_neutral x y) ; simp qsize ; lia. Qed.
#[global] Hint Rewrite qsize_qplus_neutral : qsize.*)

Lemma qplus_neutral_sound e x y : 
  qeval e (qplus_neutral x y) = qeval e x + qeval e y.
Proof.
funelim (qplus_neutral x y) ; simp qeval ; try lia.
rewrite H. lia.
Qed.
#[global] Hint Rewrite qplus_neutral_sound : qeval.

Lemma qplus_neutral_nf n x :
  n <> Q_zero -> ~is_qsucc n -> ~is_qplus n -> qnorm n -> qnorm x -> qnorm (qplus_neutral n x).
Proof.
intros H1 H2 H3 H4 H5. funelim (qplus_neutral n x) ; clear Heqcall ; try easy.
- rewrite qnorm_succ in *. now apply H.
- rewrite qnorm_plus in *. split7 ; try easy.  
  + now rewrite qnorm_plus.
  + intros (k & Hk). inv Hk.
- rewrite qnorm_plus. split7 ; try easy. intros (k & Hk). inv Hk.
- rewrite qnorm_plus. split7 ; try easy. intros (k & Hk). inv Hk.
Qed.  

(** Add two normal form quoted naturals. *)
Equations qplus : qnat -> qnat -> qnat :=
qplus Q_zero y := y ;
qplus (Q_succ x) y := Q_succ (qplus x y) ;
qplus (Q_plus x y) z := qplus x (qplus y z) ;
qplus x y := qplus_neutral x y.

(*Lemma qsize_qplus x y : 
  qsize (qplus x y) <= S (qsize x + qsize y).
Proof. funelim (qplus x y) ; simp qsize ; lia. Qed.
#[global] Hint Rewrite qsize_qplus : qsize.*)

Lemma qplus_sound e x y :
  qeval e (qplus x y) = qeval e x + qeval e y.
Proof.
funelim (qplus x y) ; simp qeval ; try lia.
+ rewrite H. lia.
+ rewrite H0, H. lia.
Qed.  
#[global] Hint Rewrite qplus_sound : qeval.

Lemma qplus_nf x y : 
  qnorm x -> qnorm y -> qnorm (qplus x y).
Proof.
intros H1 H2. funelim (qplus x y) ; clear Heqcall ; try easy.
- rewrite qnorm_succ in *. now apply H.
- rewrite qnorm_plus in H1. apply H0 ; try easy. now apply H.
- apply qplus_neutral_nf ; try easy.
  + intros (k & Hk) ; inv Hk.
  + intros (x1 & x2 & H) ; inv H.
- apply qplus_neutral_nf ; try easy.
  + intros (k & Hk) ; inv Hk.
  + intros (x1 & x2 & H) ; inv H.
Qed.

(** Helper function for [rdrop] which takes care of 
    removing left composition by the identity. *)
Equations do_shift : qnat -> ren -> ren :=
do_shift Q_zero r := r ;
do_shift k r := R_comp (R_shift k) r.

Lemma do_shift_sound e k r : 
  reval e (do_shift k r) =₁ O.rcomp (O.rshift (qeval e k)) (reval e r).
Proof. funelim (do_shift k r) ; triv. Qed.
#[global] Hint Rewrite do_shift_sound : reval.

Lemma do_shift_nf k r :
  qnorm k -> rnorm r -> (k <> Q_zero -> rnorm (R_comp (R_shift k) r)) -> rnorm (do_shift k r).
Proof. intros H1 H2 H3. funelim (do_shift k r) ; triv ; now apply H3. Qed.

(** Drop the [k] first elements in a normal form renaming [r]. *)
Equations rdrop (k : qnat) (r : ren) : ren by struct r :=
rdrop k (R_shift k') := R_shift (qplus k k') ;
rdrop k (R_mvar m) := do_shift k (R_mvar m) ;
rdrop k (R_cons i r) with k => {
  | Q_succ k' => rdrop k' r ;
  | _ => do_shift k (R_cons i r) } ;
rdrop k (R_comp (R_shift k') r) := rdrop (qplus k k') r ;
rdrop k r := do_shift k r.

Lemma rdrop_sound e k r : 
  reval e (rdrop k r) =₁ O.rcomp (O.rshift (qeval e k)) (reval e r).
Proof.
funelim (rdrop k r) ; simp reval qeval ; triv.
- now rewrite O.rshift_plus.
- rewrite H. simp qeval. now rewrite <-O.rcomp_assoc, O.rshift_plus.
Qed.
#[global] Hint Rewrite rdrop_sound : reval qeval.

Lemma rdrop_nf k r : 
  qnorm k -> rnorm r -> rnorm (rdrop k r).
Proof.
intros H1 H2. funelim (rdrop k r) ; triv.
- rewrite rnorm_shift in *. now apply qplus_nf.
- apply H.
  + rewrite rnorm_shift_l in H2. now apply qplus_nf.
  + now rewrite rnorm_shift_l in H2.
- rewrite rnorm_mvar_l in H2. destruct H2 as [H2 H3]. 
  apply do_shift_nf ; triv.
  + now rewrite rnorm_mvar_l.
  + intros H. rewrite rnorm_shift_l. split6 ; triv.
    * rewrite rnorm_mvar_l ; triv.
    * intros [H4 (? & ? & H5)]. inv H5.
- apply do_shift_nf ; triv. intros H3. rewrite rnorm_shift_l. split6 ; triv. 
  intros [_ (k' & r' & H')] ; inv H'.
- rewrite qnorm_succ in H1. rewrite rnorm_cons in H2. now apply H.
- apply do_shift_nf ; triv. intros _. rewrite rnorm_shift_l. split6 ; triv.
  intros [? _] ; triv.
- apply do_shift_nf ; triv. intros _. rewrite rnorm_shift_l. split6 ; triv.
  intros [? _] ; triv.
- apply do_shift_nf ; triv. intros _. rewrite rnorm_shift_l. split6 ; triv.
  intros [? _] ; triv.
Qed.

(** Apply a normal form renaming to a normal form quoted natural. *)
Equations rapply (r : ren) (i : qnat) : qnat by struct r := 
rapply (R_shift k) i := qplus k i ;
rapply (R_mvar m) r := Q_ren (R_mvar m) r ;
rapply (R_cons i1 r) i with i => {
  | Q_zero := i1
  | Q_succ i' := rapply r i'
  | _ := Q_ren (R_cons i1 r) i } ;
rapply (R_comp r1 r2) i with r1 => {
  | R_shift k := rapply r2 (qplus k i) ;
  | R_mvar m := rapply r2 (Q_ren (R_mvar m) i)
  | _ => (* This should not happen. *) Q_ren (R_comp r1 r2) i }.

Lemma rapply_sound e r i : 
  qeval e (rapply r i) = reval e r (qeval e i).
Proof.
funelim (rapply r i) ; simp qeval ; triv.
rewrite H. simp qeval. reflexivity.
Qed.
#[global] Hint Rewrite rapply_sound : qeval.

Lemma rapply_nf r i : 
  rnorm r -> qnorm i -> qnorm (rapply r i).
Proof. 
intros H1 H2. funelim (rapply r i) ; triv.
- rewrite rnorm_shift in H1. now apply qplus_nf.
- now rewrite qnorm_ren_mvar.
- now rewrite rnorm_cons in H1.
- rewrite rnorm_cons in H1. rewrite qnorm_succ in H2. now apply H.
- rewrite qnorm_ren_cons. rewrite rnorm_cons in H1. split5 ; triv.
- rewrite qnorm_ren_cons. rewrite rnorm_cons in H1. split5 ; triv.
- rewrite qnorm_ren_cons. rewrite rnorm_cons in H1. split5 ; triv.
- rewrite rnorm_shift_l in H1. apply H ; triv. now apply qplus_nf.
- rewrite rnorm_mvar_l in H1. apply H ; triv. now rewrite qnorm_ren_mvar.
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

Lemma rcomp_aux_nf r1 r2 :
  rnorm r1 -> rnorm r2 -> (r2 <> rid -> rnorm (R_comp r1 r2)) -> rnorm (rcomp_aux r1 r2).
Proof. 
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; triv.
all: apply H3 ; intros H ; inv H.
Qed.  

(** Compose two normal form renamings. *)
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

Lemma rcomp_nf r1 r2 : 
  rnorm r1 -> rnorm r2 -> rnorm (rcomp r1 r2).
Proof.
intros H1 H2. funelim (rcomp r1 r2) ; triv.
- rewrite rnorm_shift in H1. now apply rdrop_nf.
- rewrite rnorm_cons in * ; split.
  + now apply rapply_nf.
  + now apply H.
- apply rcomp_aux_nf ; triv. intros H. now rewrite rnorm_mvar_l.
- rewrite rnorm_shift_l in H1. apply rdrop_nf ; triv. now apply H.
- rewrite rnorm_mvar_l in H1. apply rcomp_aux_nf ; triv.  
  + now apply H.
  + intros H3. rewrite rnorm_mvar_l. split ; triv. apply H ; triv.
Qed.

(** Normalize a quoted natural. *)
Equations qnormalize : qnat -> qnat :=
qnormalize Q_zero := Q_zero ;
qnormalize (Q_succ i) := Q_succ (qnormalize i) ;
qnormalize (Q_plus x y) := qplus (qnormalize x) (qnormalize y) ;
qnormalize (Q_ren r i) := rapply (rnormalize r) (qnormalize i) ;
qnormalize (Q_mvar m) := Q_mvar m 

(** Normalize a renaming. *)
with rnormalize : ren -> ren :=
rnormalize (R_shift k) := R_shift (qnormalize k) ;
rnormalize (R_cons i r) := R_cons (qnormalize i) (rnormalize r) ;
rnormalize (R_comp r1 r2) := rcomp (rnormalize r1) (rnormalize r2) ;
rnormalize (R_mvar m) := R_mvar m.

Lemma qrnormalize_sound_aux e :
  (forall i, qeval e (qnormalize i) = qeval e i) *
  (forall r, reval e (rnormalize r) =₁ reval e r).
Proof. 
apply qnormalize_elim with 
  (P := fun i res => qeval e res = qeval e i)
  (P0 := fun r res => reval e res =₁ reval e r).
all: intros ; simp qeval reval ; triv.
- now rewrite H, H0.
- now rewrite H.
- now rewrite H, H0.
- now rewrite H, H0.
Qed.    

Lemma qnormalize_sound e i : qeval e (qnormalize i) = qeval e i.
Proof. now apply qrnormalize_sound_aux. Qed.
#[global] Hint Rewrite qnormalize_sound : qeval.

Lemma rnormalize_sound e r : reval e (rnormalize r) =₁ reval e r.
Proof. now apply qrnormalize_sound_aux. Qed.
#[global] Hint Rewrite rnormalize_sound : qeval reval.

Lemma qrnormalize_nf_aux : 
  (forall i, qnorm (qnormalize i)) * (forall r, rnorm (rnormalize r)).
Proof.
apply qnormalize_elim with (P := fun _ res => qnorm res) (P0 := fun _ res => rnorm res).
all: intros ; triv.
- now rewrite qnorm_succ.
- now apply qplus_nf.
- now apply rapply_nf.
- now rewrite rnorm_shift.
- now rewrite rnorm_cons.
- now apply rcomp_nf.
Qed.

Lemma qnormalize_nf i : qnorm (qnormalize i).
Proof. now apply qrnormalize_nf_aux. Qed.

Lemma rnormalize_nf r : rnorm (rnormalize r).
Proof. now apply qrnormalize_nf_aux. Qed.

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

Definition left := 
  O.E_ctor CApp 
    (O.E_al_cons (O.E_aterm (O.E_var (S (r (n + S m)) + n))) 
    (O.E_al_cons (O.E_aterm (O.E_var 1)) 
     O.E_al_nil)).
Definition right := O.E_var n.

From Ltac2 Require Import Printf.

Ltac2 rec coq_list (ty : constr) (xs : constr list) : constr :=
  match xs with 
  | [] => constr:(@nil $ty)
  | x :: xs =>
    let xs := coq_list ty xs in 
    constr:(@cons $ty $x $xs)
  end.

Ltac2 test_tac () : unit :=
  lazy_match! Control.goal () with 
  | @eq (O.expr Kt) ?l ?r => 
    let (e, l') := reify_expr (empty_env ()) l in 
    printf "%t" l' ;
    let e1 := coq_list constr:(nat) (e.(qnat_mvars)) in 
    let e2 := coq_list constr:(O.ren) (e.(ren_mvars)) in 
    let e3 := coq_list constr:(O.expr Kt) (e.(term_mvars)) in 
    let e4 := coq_list constr:(O.subst) (e.(subst_mvars)) in 
    printf "QNAT ENV %t" e1 ;
    printf "REN ENV %t" e2 ;
    printf "TERM ENV %t" e3 ;
    printf "SUBST ENV %t" e4 ;
    change 
      (eeval
        (fun idx => List.nth idx $e1 0) 
        (fun idx => List.nth idx $e2 O.rid) 
        (fun idx => List.nth idx $e3 (O.E_var 0))
        (fun idx => List.nth idx $e4 O.sid) 
        $l' = $r)
  | _ => Control.throw_invalid_argument "not an equality on level one terms"
  end.

Lemma test : left = right.
Proof.
unfold left, right.
ltac2:(test_tac ()).
cbv [qeval qeval_functional reval_functional 
     eeval eeval_functional nth].
Admitted.
  
