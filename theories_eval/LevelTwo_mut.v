From Prototype Require Import Prelude Sig LevelOne.

Module Make (S : Sig).
Module O := LevelOne.Make (S).
Definition arg_ty := @arg_ty (base S.t).

(*********************************************************************************)
(** *** Quoted naturals and explicit renamings. *)
(*********************************************************************************)

(** Quoted natural. *)
Inductive qnat :=
| Q_zero : qnat 
| Q_succ : qnat -> qnat 
| Q_mvar : nat -> qnat.

Notation "'Q_one'" := (Q_succ Q_zero).

(** Explicit renaming. *)
Inductive ren :=
| R_shift : qnat -> ren
| R_cons : qnat -> ren -> ren
| R_comp : ren -> ren -> ren 
| R_mvar : O.ren -> ren.

(*********************************************************************************)
(** *** Expressions and explicit substitutions. *)
(*********************************************************************************)

(** Kind of an expression. *)
Inductive kind :=
(** Term. *)
| Kt : kind
(** Constructor argument. *)
| Ka : arg_ty -> kind
(** List of constructor arguments. *)
| Kal : list arg_ty -> kind.
Derive NoConfusion for kind.

Definition eval_kind (k : kind) : O.kind :=
  match k with Kt => O.Kt | Ka ty => O.Ka ty | Kal tys => O.Kal tys end.

(** Type of an expressions metavariable. *)
Definition mvar (k : kind) := O.expr (eval_kind k).

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
(** Expression metavariable. *)
| E_mvar {k} : mvar k -> expr k

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
| S_mvar : O.subst -> subst

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
Definition up_ren (r : ren) : ren :=
  R_cons Q_zero (R_comp r (R_shift Q_one)).

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  S_cons (E_tvar Q_zero) (S_comp s (S_shift Q_one)).

(*********************************************************************************)
(** *** Evalutation. *)
(*********************************************************************************)

Equations eval_qnat : qnat -> nat :=
eval_qnat Q_zero := 0 ;
eval_qnat (Q_succ i) := S (eval_qnat i) ;
eval_qnat (Q_mvar x) := x.

Equations eval_ren : ren -> O.ren :=
eval_ren (R_shift i) := O.rshift (eval_qnat i) ;
eval_ren (R_cons i r) := O.rcons (eval_qnat i) (eval_ren r) ;
eval_ren (R_comp r1 r2) := O.rcomp (eval_ren r1) (eval_ren r2) ;
eval_ren (R_mvar x) := x.

Equations eval_expr {k} : expr k -> O.expr (eval_kind k) :=
eval_expr (E_tvar i) := O.E_var (eval_qnat i) ;
eval_expr (E_tctor c al) := O.E_ctor c (eval_expr al) ;
eval_expr E_al_nil := O.E_al_nil ;
eval_expr (E_al_cons a al) := O.E_al_cons (eval_expr a) (eval_expr al) ;
eval_expr (E_abase b x) := O.E_abase b x ;
eval_expr (E_aterm t) := O.E_aterm (eval_expr t) ;
eval_expr (E_abind a) := O.E_abind (eval_expr a) ;
eval_expr (E_ren e r) := O.rename (eval_expr e) (eval_ren r) ;
eval_expr (E_subst e s) := O.substitute (eval_expr e) (eval_subst s) ;
eval_expr (E_mvar x) := x

with eval_subst : subst -> O.subst :=
eval_subst (S_shift k) := O.sshift (eval_qnat k) ;
eval_subst (S_cons t s) := O.scons (eval_expr t) (eval_subst s) ;
eval_subst (S_comp s1 s2) := O.scomp (eval_subst s1) (eval_subst s2) ;
eval_subst (S_ren r) := O.rscomp (eval_ren r) O.E_var ;
eval_subst (S_mvar x) := x.

(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

(** Add a natural with a quoted natural. *)
Equations qadd_aux : nat -> qnat -> qnat :=
qadd_aux x Q_zero := Q_mvar x ;
qadd_aux x (Q_succ y) := Q_succ (qadd_aux x y) ;
qadd_aux x (Q_mvar y) := Q_mvar (x + y).    

Lemma qadd_aux_sound x y : eval_qnat (qadd_aux x y) = x + eval_qnat y.
Proof. funelim (qadd_aux x y) ; simp eval_qnat ; lia. Qed.
#[global] Hint Rewrite qadd_aux_sound : eval_qnat.

(** Add two quoted naturals. *)
Equations qadd : qnat -> qnat -> qnat :=
qadd Q_zero y := y ;
qadd (Q_succ x) y := Q_succ (qadd x y) ;
qadd (Q_mvar x) y := qadd_aux x y.

Lemma qadd_sound x y : 
  eval_qnat (qadd x y) = eval_qnat x + eval_qnat y.
Proof. funelim (qadd x y) ; simp eval_qnat ; lia. Qed.
#[global] Hint Rewrite qadd_sound : eval_qnat.

Ltac2 rec reify_nat (t : constr) : constr := 
  lazy_match! t with 
  | 0 => constr:(Q_zero)
  | S ?i =>
    let i := reify_nat i in 
    constr:(Q_succ $i)
  | ?x + ?y => 
    let x := reify_nat x in 
    let y := reify_nat y in 
    constr:(qadd $x $y)
  | ?i => constr:(Q_mvar $i)
  end

with reify_ren (t : constr) : constr :=
  lazy_match! t with 
  | O.rshift ?k =>
    let k := reify_nat k in 
    constr:(R_shift $k) 
  | O.rcons ?i ?r =>
    let i := reify_nat i in 
    let r := reify_ren r in 
    constr:(R_cons $i $r)
  | O.rcomp ?r1 ?r2 =>
    let r1 := reify_ren r1 in 
    let r2 := reify_ren r2 in 
    constr:(R_comp $r1 $r2)
  | ?r => constr:(R_mvar $r)
  end.

Ltac2 rec reify_expr (t : constr) : constr :=
  lazy_match! t with 
  | O.E_var ?i => 
    let i := reify_nat i in
    constr:(E_tvar $i)
  | O.E_ctor ?c ?al => 
    let al := reify_expr al in
    constr:(E_tctor $c $al)
  | O.E_al_nil => constr:(E_al_nil)
  | O.E_al_cons ?a ?al => 
    let a := reify_expr a in
    let al := reify_expr al in
    constr:(E_al_cons $a $al)
  | O.E_abase ?b ?x => constr:(E_abase $b $x)
  | O.E_aterm ?t => 
    let t := reify_expr t in
    constr:(E_aterm $t)
  | O.E_abind ?a =>
    let a := reify_expr a in
    constr:(E_abind $a)
  | O.rename ?t ?r =>
    let t := reify_expr t in
    let r := reify_ren r in
    constr:(E_ren $t $r)
  | O.substitute ?t ?s =>
    let t := reify_expr t in
    let s := reify_subst s in
    constr:(E_subst $t $s)
  | _ => constr:(@E_mvar Kt $t)
  end

with reify_subst (s : constr) : constr :=
  lazy_match! s with 
  | O.sid => constr:(sid)
  | O.sshift ?k => 
    let k := reify_nat k in 
    constr:(S_shift $k)
  | O.scons ?t ?s =>
    let t := reify_expr t in 
    let s := reify_subst s in 
    constr:(S_cons $t $s)
  | O.scomp ?s1 ?s2 =>
    let s1 := reify_subst s1 in 
    let s2 := reify_subst s2 in 
    constr:(S_comp $s1 $s2)
  | O.srcomp ?s ?r =>
    let s := reify_subst s in 
    let r := reify_ren r in
    constr:(S_comp $s (S_ren $r))
  | O.rscomp ?r ?s =>
    let r := reify_ren r in
    let s := reify_subst s in 
    constr:(S_comp (S_ren $r) $s)
  | ?s => constr:(S_mvar $s)
  end.
  
(*********************************************************************************)
(** *** Normal forms. *)
(*********************************************************************************)

(** The goal of normal forms is not to precisely capture the structure
    of simplified terms/substitutions: rather, they add some structure 
    above plain terms/substitutions, while still remaining simple to work with.
    
    In particular, normal forms are not unique, and all functions 
    [term -> nf_term] are not equivalent. *)

(** Normal form renamings: the left hand side of a composition
    can't be a cons or a composition. *)
Inductive nf_ren : Type :=
(** [NR_shift k] represents [R_shift k]. *)
| NR_shift : qnat -> nf_ren
(** [NR_cons i r] represents [R_cons i r]. *)
| NR_cons : qnat -> nf_ren -> nf_ren 
(** [NR_comp_shift k r] represents [R_comp (R_shift k) r]. *)
| NR_comp_shift : qnat -> nf_ren -> nf_ren 
(** [NR_comp_mvar x r] represents [R_comp (R_mvar x) r]. *)
| NR_comp_mvar : O.ren -> nf_ren -> nf_ren 
(** [NR_mvar x] represents [R_mvar x]. *)
| NR_mvar : O.ren -> nf_ren.

Reserved Notation "'nf_term'" (at level 0).
Reserved Notation "'nf_arg' ty" (at level 0, ty at level 0).
Reserved Notation "'nf_args' tys" (at level 0, tys at level 0).

Inductive nf_expr : kind -> Type :=
| NE_tvar : qnat -> nf_term
| NE_tctor : forall c, nf_args (ctor_type S.t c) -> nf_term
| NE_al_nil : nf_args []
| NE_al_cons {ty tys} : nf_arg ty -> nf_args tys -> nf_args (ty :: tys)
| NE_abase : forall b, denote_base S.t b -> nf_arg (AT_base b)
| NE_aterm : nf_term -> nf_arg AT_term
| NE_abind {ty} : nf_arg ty -> nf_arg (AT_bind ty)
| NE_mvar {k} : mvar k -> nf_expr k
(** Renaming/substitution blocked on a metavariable. *)
| NE_ren_mvar_r {k} : mvar k -> nf_ren -> nf_expr k
| NE_subst_mvar_s {k} : mvar k -> nf_subst -> nf_expr k
(** Renaming/susbtitution blocked on a variable. *)
| NE_ren_var : qnat -> nf_ren -> nf_term
| NE_subst_var : qnat -> nf_subst -> nf_term

(** Normal form substitutions: the left hand side of a composition
    can't be a cons or a composition. *)
with nf_subst : Type :=
| NS_shift : qnat -> nf_subst 
| NS_cons : nf_term -> nf_subst -> nf_subst 
| NS_comp_shift : qnat -> nf_subst -> nf_subst 
| NS_comp_ren : nf_ren -> nf_subst -> nf_subst 
| NS_comp_mvar : O.subst -> nf_subst -> nf_subst 
| NS_ren : nf_ren -> nf_subst
| NS_mvar : O.subst -> nf_subst

where "'nf_term'" := (nf_expr Kt)
  and "'nf_arg' ty" := (nf_expr (Ka ty))
  and "'nf_args' tys" := (nf_expr (Kal tys)).

Equations eval_nf_ren : nf_ren -> O.ren :=
eval_nf_ren (NR_shift k) := O.rshift (eval_qnat k) ;
eval_nf_ren (NR_cons i r) := O.rcons (eval_qnat i) (eval_nf_ren r) ;
eval_nf_ren (NR_comp_shift k r) := O.rcomp (O.rshift (eval_qnat k)) (eval_nf_ren r) ;
eval_nf_ren (NR_comp_mvar x r) := O.rcomp x (eval_nf_ren r) ;
eval_nf_ren (NR_mvar x) := x.

Equations eval_nf_expr {k} : nf_expr k -> O.expr (eval_kind k) :=
eval_nf_expr (NE_tvar i) := O.E_var (eval_qnat i) ;
eval_nf_expr (NE_tctor c al) := O.E_ctor c (eval_nf_expr al) ;
eval_nf_expr NE_al_nil := O.E_al_nil ;
eval_nf_expr (NE_al_cons a al) := O.E_al_cons (eval_nf_expr a) (eval_nf_expr al) ;
eval_nf_expr (NE_abase b x) := O.E_abase b x ;
eval_nf_expr (NE_aterm t) := O.E_aterm (eval_nf_expr t) ;
eval_nf_expr (NE_abind a) := O.E_abind (eval_nf_expr a) ;
eval_nf_expr (NE_mvar x) := x ;
eval_nf_expr (NE_ren_mvar x r) := O.rename x (eval_nf_ren r) ;
eval_nf_expr (NE_subst_mvar x s) := O.substitute x (eval_nf_subst s) ;
eval_nf_expr (NE_ren_var i r) := eval_nf_ren r (eval_qnat i) ;
eval_nf_expr (NE_subst_var i s) := eval_nf_subst s (eval_qnat i) 

with eval_nf_subst : nf_subst -> O.subst :=
eval_nf_subst (NS_shift k) := O.sshift k ;
eval_nf_subst (NS_cons t s) := O.scons (eval_nf_expr t) (eval_nf_subst s) ;
eval_nf_subst (NS_comp_shift k s) := O.scomp 
.

(*********************************************************************************)
(** *** Simplification. *)
(*********************************************************************************)


(** Apply a normal form renaming to a quoted natural. *)
Equations rapply : nf_ren -> qnat -> qnat :=
rapply (NR_shift k) i := qadd k i ;
rapply (NR_cons k _) Q_zero := k ;
rapply (NR_cons _ r) (Q_succ i) := rapply r i ;
rapply (NR_cons k r) (Q_mvar i) := Q_mvar (eval_nf_ren (NR_cons k r) i) ;
rapply (NR_comp_shift k r) i := rapply r (qadd k i) ;
rapply (NR_comp_mvar x r) i := rapply r (Q_mvar (x (eval_qnat i))) ;
rapply (NR_mvar x) i := Q_mvar (x (eval_qnat i)).

Lemma rapply_sound r i : 
  eval_qnat (rapply r i) = eval_ren r (eval_qnat i).
Proof. 
funelim (rapply r i) ; simp eval_qnat eval_ren ; try solve [ auto ].
rewrite H0, H. reflexivity.
Qed.
#[global] Hint Rewrite rapply_sound : eval_qnat.

(** Tail of a normal form renaming. *)
Equations rtail : nf_ren -> nf_ren := 
rtail (N_rshift k) := N_rshift (qS k) ;
rtail (N_rcons _ r) := r ;
rtail (N_rcomp k xr r) := N_rcomp (qS k) xr r.

Lemma rtail_sound r : eval_nf (rtail r) =₁ O.rcomp (O.rshift 1) (eval_nf r).
Proof. 
funelim (rtail r) ; simp rtail eval_nf eval_qnat.
- now rewrite O.rshift_succ_l.
- now rewrite O.rshift_rcons.
- repeat rewrite <-O.rcomp_assoc. now rewrite O.rshift_succ_l.
Qed. 
#[global] Hint Rewrite rtail_sound : eval_nf.    

(** Drop the first [k] elements in a normal form renaming. *)
Equations rdrop : qnat -> nf_ren -> nf_ren :=
rdrop q0 r := r ;
rdrop (qS k) r := rtail (rdrop k r) ;
rdrop (qAtom k) r := N_rcomp (qAtom k) O.rid r.

Lemma rdrop_sound k r : 
  eval_nf (rdrop k r) =₁ O.rcomp (O.rshift (eval_qnat k)) (eval_nf r).
Proof.
funelim (rdrop k r) ; simp eval_nf eval_qnat.
- now rewrite O.rcomp_rid_l.
- rewrite H. now rewrite <-O.rcomp_assoc, O.rshift_succ_l.
- now rewrite O.rcomp_rid_r. 
Qed.  
#[global] Hint Rewrite rdrop_sound : eval_nf.    

(** Apply a normal form renaming to a de Bruijn index. *)
Equations rapply : nf_ren -> qnat -> qnat :=
rapply (N_rshift k) i := qadd k i ;
rapply (N_rcons i _) q0 := i ;
rapply (N_rcons _ r) (qS k) := rapply r k ;
rapply (N_rcons i r) (qAtom k) := qAtom (eval_nf (N_rcons i r) k) ;
rapply (N_rcomp k xr r) i := rapply r (qAtom (xr (eval_qnat (qadd k i)))).

Lemma rapply_sound r i : 
  eval_qnat (rapply r i) = eval_nf r (eval_qnat i).
Proof. funelim (rapply r i) ; now simp eval_nf eval_qnat in *. Qed.
#[global] Hint Rewrite rapply_sound : eval_nf.    
    
(** Compose two normal form renamings. *)
Equations rcomp : nf_ren -> nf_ren -> nf_ren :=
rcomp (N_rshift k) r := rdrop k r ;
rcomp (N_rcons i r1) r2 := N_rcons (rapply r2 i) (rcomp r1 r2) ;
rcomp (N_rcomp k xr r1) r2 := N_rcomp k xr (rcomp r1 r2).

Lemma rcomp_sound r1 r2 : 
  eval_nf (rcomp r1 r2) =₁ O.rcomp (eval_nf r1) (eval_nf r2).
Proof.
funelim (rcomp r1 r2) ; simp eval_nf eval_qnat in *.
- reflexivity.
- now rewrite O.rcomp_rcons_distrib, H.
- rewrite H. now repeat rewrite O.rcomp_assoc.
Qed.
#[global] Hint Rewrite rcomp_sound : eval_nf.    

(** Lift a normal form renaming through a binder. *)
Equations rup : nf_ren -> nf_ren :=
rup r := N_rcons q0 (rcomp r (N_rshift q1)).

Lemma rup_sound r : eval_nf (rup r) =₁ O.up_ren (eval_nf r).
Proof. simp rup eval_nf. reflexivity. Qed.

(** Instantiate a normal form term with a normal form renaming. *)
Equations rinst {k} : nf_expr (K1 k) -> nf_ren -> nf_expr (K1 k) :=
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
  (forall k (t : nf_expr (K1 k)) r, 
    eval_nf (rinst t r) = O.rename (eval_nf t) (eval_nf r)) *
  (forall s r, 
    eval_nf (srcomp s r) =₁ fun i => O.rename (eval_nf s i) (eval_nf r)).
Proof.
apply rinst_elim with 
  (P := fun k (t : nf_expr (K1 k)) (r : nf_ren) (res : nf_expr (K1 k))  => 
    eval_nf res = O.rename (eval_nf t) (eval_nf r))
  (P0 := fun (s : nf_subst) (r : nf_ren) (res : nf_subst) =>
    eval_nf res =₁ fun i => O.rename (eval_nf s i) (eval_nf r)).
all: try (intros ; now simp eval_nf).
- intros c al r H. simp eval_nf. rewrite H. now simp rename.
- intros ty tys a al r H1 H2. simp eval_nf rename. now rewrite H1, H2.
- intros t r H. simp eval_nf rename. now rewrite H.
- intros ty a r H. simp eval_nf rename. now rewrite H, rup_sound.
- intros k xt r1 r2. destruct k ; simp eval_nf ; now rewrite O.ren_ren.
- intros k xt s r H. destruct k ; simp eval_nf ; now rewrite H, O.subst_ren.
- intros i xs s r H. simp eval_nf substitute. cbv [O.scomp]. 
  now rewrite H, O.subst_ren.
- intros k r. simp eval_nf. intros i. rewrite rdrop_sound. reflexivity.
- intros t s r H1 H2. simp eval_nf. rewrite H1, H2. intros [|i] ; reflexivity.
- intros k xs s r H. simp eval_nf. rewrite H. intros i. cbv [O.scomp O.sshift].
  simp substitute. now rewrite O.subst_ren.
- intros r1 r2. simp eval_nf. intros i. simp rename. now rewrite rcomp_sound.
Qed.

Lemma rinst_sound k (t : nf_expr (K1 k)) r :   
  eval_nf (rinst t r) = O.rename (eval_nf t) (eval_nf r).
Proof. now apply rinst_srcomp_sound_aux. Qed.

Lemma srcomp_sound s r :
  eval_nf (srcomp s r) =₁ fun i => O.rename (eval_nf s i) (eval_nf r).
Proof. now apply rinst_srcomp_sound_aux. Qed.

(** Apply a normal form substitution to a de Bruijn index. *)
Equations sapply : nf_subst -> qnat -> nf_term :=
sapply (N_sshift k) i := N_tvar (qadd k i) ;
sapply (N_scons t _) q0 := t ;
sapply (N_scons _ s) (qS i) := sapply s i ;
sapply (N_scons t s) (qAtom i) := @N_sinst_l Kt (eval_nf (N_scons t s) i) (N_sshift q0) ;
sapply (N_scomp k xs s) i := N_sinst_r (qadd k i) xs s ;
sapply (N_sren r) i := N_tvar (rapply r i).  

Lemma sapply_sound s i : eval_nf (sapply s i) = eval_nf s i.
Proof. 
funelim (sapply s i) ; simp eval_nf ; try reflexivity.
- now rewrite H.
- now rewrite rapply_sound.
Qed.    

(** Tail of a normal form substitution. *)
Equations stail : nf_subst -> nf_subst :=
stail (N_sshift k) := N_sshift (S k) ;
stail (N_scons t s) := s ;
stail (N_scomp k xs s) := N_scomp (S k) xs s ;
stail (N_sren r) := N_sren (rtail r).

Lemma stail_sound s : eval_nf (stail s) =₁ O.scomp (O.sshift 1) (eval_nf s).
Proof. 
funelim (stail s) ; simp eval_nf.
- now rewrite O.sshift_succ_l.
- now rewrite O.sshift_scons.
- repeat rewrite <-O.scomp_assoc. now rewrite O.sshift_succ_l.
- intros i. now rewrite rtail_sound.
Qed.

(** Drop the first [k] elements in a normal form substitution. *)
Equations sdrop : nat -> nf_subst -> nf_subst :=
sdrop 0 s := s ;
sdrop (S k) s := stail (sdrop k s).

Lemma sdrop_sound k s : eval_nf (sdrop k s) =₁ O.scomp (O.sshift k) (eval_nf s).
Proof.
funelim (sdrop k s) ; simp eval_nf.
- now rewrite O.scomp_sid_l.
- rewrite stail_sound, H. now rewrite <-O.scomp_assoc, O.sshift_succ_l.
Qed.  

(** Lift a normal form substitution through a binder. *)
Equations sup : nf_subst -> nf_subst :=
sup s := N_scons (N_tvar 0) (srcomp s (N_rshift 1)).

Lemma sup_sound s : eval_nf (sup s) =₁ O.up_subst (eval_nf s).
Proof. simp sup eval_nf. unfold O.up_subst. now rewrite srcomp_sound. Qed.

(** Compose a normal form renaming with a normal form substitution. *)
Equations rscomp : nf_ren -> nf_subst -> nf_subst :=
rscomp (N_rshift k) s := sdrop k s ;
rscomp (N_rcons i r) s := N_scons (sapply s i) (rscomp r s) ;
rscomp (N_rcomp k xr r) s := N_scomp k (fun i => O.E_var (xr i)) (rscomp r s).

Lemma rscomp_sound r s : 
  eval_nf (rscomp r s) =₁ fun i => eval_nf s (eval_nf r i).
Proof.
funelim (rscomp r s) ; simp eval_nf.
- now rewrite sdrop_sound.
- rewrite sapply_sound, H. intros [|] ; reflexivity.
- now rewrite H.
Qed.     

(** Instantiate a normal form expression with a normal form substitution. *)
Equations sinst {k} (t : nf_expr (K1 k)) (s : nf_subst) : nf_expr (K1 k) by struct t :=
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
scomp (N_scons t s1) s2 := N_scons (sinst t s2) (scomp s1 s2) ;
scomp (N_scomp k xs s1) s2 := N_scomp k xs (scomp s1 s2) ; 
scomp (N_sren r) s := rscomp r s.

Lemma sinst_scomp_sound_aux : 
  (forall k (t : nf_expr (K1 k)) s, 
    eval_nf (sinst t s) = O.substitute (eval_nf t) (eval_nf s)) *
  (forall s1 s2, 
    eval_nf (scomp s1 s2) =₁ O.scomp (eval_nf s1) (eval_nf s2)).
Proof.
apply sinst_elim with 
  (P := fun k (t : nf_expr (K1 k)) (s : nf_subst) (res : nf_expr (K1 k))  => 
    eval_nf res = O.substitute (eval_nf t) (eval_nf s))
  (P0 := fun (s1 s2 res : nf_subst) =>
    eval_nf res =₁ O.scomp (eval_nf s1) (eval_nf s2)).
- intros i s. now rewrite sapply_sound.
- intros c al s H. simp eval_nf. now rewrite H.
- reflexivity.
- intros ty tys a al s H1 H2. simp eval_nf substitute. now rewrite H1, H2.
- intros b x s. now simp eval_nf substitute.
- intros t s H. simp eval_nf substitute. now rewrite H.
- intros ty a s H. simp eval_nf substitute. now rewrite H, sup_sound.
- intros k xt r s. destruct k ; simp eval_nf substitute.
  all: now rewrite rscomp_sound, O.ren_subst.
- intros k xt s1 s2 H. destruct k ; simp eval_nf substitute.
  all: now rewrite H, O.subst_subst.
- intros i xr r s. simp eval_nf substitute rename.
  cbv [O.scomp]. simp substitute. now rewrite rscomp_sound.
- intros i xs s1 s2 H. simp eval_nf substitute. 
  cbv [O.scomp]. now rewrite H, O.subst_subst.
- intros k s. simp eval_nf. now rewrite sdrop_sound.
- intros t s1 s2 H1 H2. simp eval_nf. rewrite H1, H2.
  now rewrite O.scomp_scons_distrib.
- intros k xs s1 s2 H. simp eval_nf. rewrite H. now repeat rewrite O.scomp_assoc.
- intros r s. rewrite rscomp_sound. reflexivity.
Qed. 
    