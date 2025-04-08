From Equations Require Import Equations.
From Ltac2 Require Import Ltac2.
From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo LevelTwoNF.

Module Make (S : Sig).
Module NF := LevelTwoNF.Make (S).
Module T := NF.T.
Module O := T.O.
Notation denote_type := T.denote_type.

(*********************************************************************************)
(** *** Denotation (level two -> level one). *)
(*********************************************************************************)

(** Mapping from level two expressions to level one expressions and substitutions. *)
Equations denote {k} (t : T.expr k) : denote_type k by struct t :=
denote (T.E_var i) := O.E_var i ;
denote (T.E_ctor c al) := O.E_ctor c (denote al) ;
denote T.E_al_nil := O.E_al_nil ;
denote (T.E_al_cons a al) := O.E_al_cons (denote a) (denote al) ;
denote (T.E_abase b x) := O.E_abase b x ;
denote (T.E_aterm t) := O.E_aterm (denote t) ;
denote (T.E_abind a) := O.E_abind (denote a) ;
denote (@T.E_subst T.Kt t s) := O.substitute (denote t) (denote s) ;
denote (@T.E_subst (T.Ka _) t s) := O.substitute (denote t) (denote s) ;
denote (@T.E_subst (T.Kal _) t s) := O.substitute (denote t) (denote s) ;
denote (T.E_sshift k) := O.sshift k ;
denote (T.E_scons t s) := O.scons (denote t) (denote s) ;
denote (T.E_scomp s1 s2) := O.scomp (denote s1) (denote s2) ;
denote (T.E_mvar x) := x.

(*********************************************************************************)
(** *** Correctness of denotation. *)
(*********************************************************************************)

(** Equality on denoted expressions. We use pointwise equality 
    for substitutions so as to not assume functional extensionality. *)
Definition denote_rel (k : T.kind) : relation (denote_type k) :=
  match k with 
  | T.Ks => @point_eq nat (O.expr O.Kt)
  | _ => eq
  end.

#[global] Instance denote_rel_equiv k : Equivalence (denote_rel k).
Proof. 
constructor ; destruct k ; try solve [ easy ].
- intros ?????. etransitivity ; eauto.
- intros ?????. etransitivity ; eauto.
Qed.

(** Main correctness result for [denote]: it transports level-two _sigma-equal_ terms 
    to level-one _equal_ terms. *)
#[global] Instance denote_proper {k} : Proper (T.axiom_eq ==> denote_rel k) (@denote k).
Proof.
intros t1 t2 Ht. induction Ht ; simpl in * ; simp denote.
all: try solve [ auto | easy ].
- etransitivity ; eauto. 
- destruct k ; simp denote ; now apply O.substitute_proper.
- now apply O.scons_proper.
- now apply O.scomp_proper.
- simp substitute. f_equal. apply O.substitute_proper ; auto.
  simp up_subst denote. rewrite O.up_subst_alt. reflexivity.
- destruct k ; simp denote ; now rewrite O.subst_subst.
- destruct k ; unfold T.sid ; simp denote ; now rewrite O.subst_sid.
- now rewrite O.sid_scons.
- unfold T.sid ; simp denote. now rewrite O.scomp_id_r.
- now rewrite O.scomp_assoc.
- now rewrite O.scomp_scons_distrib.
Qed.

(*********************************************************************************)
(** *** Reification (level one -> level two). *)
(*********************************************************************************)

(** Compute the kind [k : T.kind] such that [denote_type k = type of e]. *)
(*Ltac2 inv_denote_type (e : constr) : constr :=
  lazy_match! Constr.type e with
  | O.expr O.Kt => constr:(T.Km T.Kt)
  | O.expr (O.Ka ?ty) => constr:(T.Km (O.Ka $ty))
  | O.expr (O.Kal ?tys) => constr:(T.Km (O.Kal $tys))
  | O.subst => constr:(T.Ks)
  | nat -> O.expr O.Kt => constr:(T.Ks)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "inv_denote_type")))
  end.*)

(** Convert an Ltac2 integer to a Rocq term of type [nat]. *)
(*Ltac2 rec nat_of_int (i : int) : constr :=
  if Int.le i 0 then constr:(0) 
  else let i' := nat_of_int (Int.sub i 1) in constr:(S $i').*)

(** Create a new metavariable for term/substitution [t] and add it to the map [m].
    If [t] is already present in [m], we don't add it twice. *)
(*Ltac2 make_mvar (m : map) (t : constr) : map * constr :=
  match List.find_opt (fun (_, _, t') => Constr.equal t t') m with 
  (** [t] is already in the environment [m] at position [idx]. *)
  | Some (idx, k, _) => constr:(@T.E_mvar $k $idx)
  (** [t] is not in the environment: we have to add it to [m]. *)
  | None => 
    let idx := nat_of_int (List.length m) in
    let k := inv_denote_type t in
    List.append m [ (idx, k, t) ], constr:(@T.E_mvar $k $idx)
  end.*)

Ltac2 rec reify_term (t : constr) : constr :=
  lazy_match! t with 
  | O.E_var ?i => constr:(T.E_var $i)
  | O.E_ctor ?c ?al => 
    let al := reify_term al in
    constr:(T.E_ctor $c $al)
  | O.E_al_nil => constr:(T.E_al_nil)
  | O.E_al_cons ?a ?al => 
    let a := reify_term a in
    let al := reify_term al in
    constr:(T.E_al_cons $a $al)
  | O.E_abase ?b ?x => constr:(T.E_abase $b $x)
  | O.E_aterm ?t => 
    let t := reify_term t in
    constr:(T.E_aterm $t)
  | O.E_abind ?a =>
    let a := reify_term a in
    constr:(T.E_abind $a)
  | O.substitute ?t ?s =>
    let t := reify_term t in
    let s := reify_subst s in
    constr:(T.E_subst $t $s)
  | _ => constr:(@T.E_mvar (T.Km T.Kt) $t)
  end
with reify_subst (s : constr) : constr :=
  lazy_match! s with 
  | O.sid => constr:(T.E_sshift 0)
  | O.sshift ?k => constr:(T.E_sshift $k)
  | O.scons ?t ?s =>
    let t := reify_term t in 
    let s := reify_subst s in 
    constr:(T.E_scons $t $s)
  | O.up_subst ?s =>
    let s := reify_subst s in 
    constr:(T.up_subst $s)
  | ?s => constr:(@T.E_mvar T.Ks $s)
  end.

  Print T.up_subst.
  Print O.up_subst.
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

Module OT := Make (S).
Import OT.

Axiom t1 : O.expr O.Kt.
Axiom t2 : O.expr O.Kt.
Axiom tau : O.subst.

Definition left := 
  O.substitute 
    (O.substitute t1 (O.scons (O.E_var 0) (O.scomp tau (O.sshift 1)))) 
    (O.scons (O.substitute t2 tau) O.sid).

Definition right := 
  O.substitute 
    (O.substitute t1 (O.scons t2 O.sid))
    tau.

From Ltac2 Require Import Printf.

Ltac2 test_tac () : unit :=
  lazy_match! Control.goal () with 
  | @eq (O.expr O.Kt) ?l1 ?r1 => 
    let l2 := reify_term l1 in 
    let r2 := reify_term r1 in 
    printf "%t" l2 ;
    printf "%t" r2 ;
    change (denote $l2 = denote $r2) ;
    rewrite <-(NF.normalize_sound $l2) ;
    rewrite <-(NF.normalize_sound $r2)
  | _ => Control.throw_invalid_argument "not an equality on level one terms"
  end.

Lemma test : left = right.
Proof.
unfold left, right.
ltac2:(test_tac ()).
apply (@denote_proper (T.Km T.Kt)).
simp normalize ssubst. reflexivity. simp ssubst.

apply T.aeq_congr_subst.

reflexivity. 

Definition t2 : T.expr (T.Km T.Kt). 
ltac2:(refine (reify_term constr:(
  O.E_ctor CApp
    (O.E_al_cons (O.E_aterm (O.substitute t (fun i => O.E_var i)))
    (O.E_al_cons (O.E_aterm t)
     O.E_al_nil))))).
Defined.

Print t2.

Lemma test : denote t2 = 
  O.E_ctor CApp
    (O.E_al_cons (O.E_aterm (O.substitute t (fun i => O.E_var i)))
    (O.E_al_cons (O.E_aterm t)
     O.E_al_nil)).
Proof. reflexivity. Qed.

Eval cbv [denote] simpl. in denote t'.

Let t