From Equations Require Import Equations.
From Ltac2 Require Import Ltac2.
From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo.

Module Make (S : Sig).
Module O := LevelOne.Make (S).
Module T := LevelTwo.Make (S).

(*********************************************************************************)
(** *** Denotation (level two -> level one). *)
(*********************************************************************************)

Definition denote_type (k : T.kind) : Type :=
  match k with 
  | T.Ks => O.subst
  | T.Km T.Kt => O.expr O.Kt
  | T.Km (T.Kal tys) => O.expr (O.Kal tys)
  | T.Km (T.Ka ty) => O.expr (O.Ka ty)
  end.
      
(** Denotation doesn't know how to handle metavariables: it thus works up to an
    assignment, which determines how to denote metavariables. *)
Definition assignment := forall k : T.kind, T.mvar k -> denote_type k.

(** Mapping from level two expressions to level one expressions and substitutions. *)
Equations denote {k} (m : assignment) (t : T.expr k) : denote_type k by struct t :=
denote m (T.E_var i) := O.E_var i ;
denote m (T.E_ctor c al) := O.E_ctor c (denote m al) ;
denote m T.E_al_nil := O.E_al_nil ;
denote m (T.E_al_cons a al) := O.E_al_cons (denote m a) (denote m al) ;
denote m (T.E_abase b x) := O.E_abase b x ;
denote m (T.E_aterm t) := O.E_aterm (denote m t) ;
denote m (T.E_abind a) := O.E_abind (denote m a) ;
denote m (@T.E_subst T.Kt t s) := O.substitute (denote m t) (denote m s) ;
denote m (@T.E_subst (T.Ka _) t s) := O.substitute (denote m t) (denote m s) ;
denote m (@T.E_subst (T.Kal _) t s) := O.substitute (denote m t) (denote m s) ;
denote m (T.E_sshift k) := O.sshift k ;
denote m (T.E_scons t s) := O.scons (denote m t) (denote m s) ;
denote m (T.E_scomp s1 s2) := O.scomp (denote m s1) (denote m s2) ;
denote m (T.E_mvar x) := m _ x.

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
#[global] Instance denote_proper {k} m : Proper (T.axiom_eq ==> denote_rel k) (@denote k m).
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

(** We use a [map] to store level one term/substitutions that we could not reify. *)
Ltac2 Type map := (constr * constr * constr) list.

(** Compute the kind [k : T.kind] such that [denote_type k = type of e]. *)
Ltac2 inv_denote_type (e : constr) : constr :=
  lazy_match! Constr.type e with
  | O.expr O.Kt => constr:(T.Km T.Kt)
  | O.expr (O.Ka ?ty) => constr:(T.Km (O.Ka $ty))
  | O.expr (O.Kal ?tys) => constr:(T.Km (O.Kal $tys))
  | O.subst => constr:(T.Ks)
  | nat -> O.expr O.Kt => constr:(T.Ks)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "inv_denote_type")))
  end.

(** Convert an Ltac2 integer to a Rocq term of type [nat]. *)
Ltac2 rec nat_of_int (i : int) : constr :=
  if Int.le i 0 then constr:(0) 
  else let i' := nat_of_int (Int.sub i 1) in constr:(S $i').

(** Create a new metavariable for term/substitution [t] and add it to the map [m].
    If [t] is already present in [m], we don't add it twice. *)
Ltac2 make_mvar (m : map) (t : constr) : map * constr :=
  match List.find_opt (fun (_, _, t') => Constr.equal t t') m with 
  (** [t] is already in the environment [m] at position [idx]. *)
  | Some (idx, k, _) => m, constr:(@T.E_mvar $k $idx)
  (** [t] is not in the environment: we have to add it to [m]. *)
  | None => 
    let idx := nat_of_int (List.length m) in
    let k := inv_denote_type t in
    List.append m [ (idx, k, t) ], constr:(@T.E_mvar $k $idx)
  end.    

Ltac2 rec reify_term (m : map) (t : constr) : map * constr :=
  lazy_match! t with 
  | O.E_var ?i => m, constr:(T.E_var $i)
  | O.E_ctor ?c ?al => 
    let (m, al) := reify_term m al in
    m, constr:(T.E_ctor $c $al)
  | O.E_al_nil => m, constr:(T.E_al_nil)
  | O.E_al_cons ?a ?al => 
    let (m, a) := reify_term m a in
    let (m, al) := reify_term m al in
    m, constr:(T.E_al_cons $a $al)
  | O.E_abase ?b ?x => m, constr:(T.E_abase $b $x)
  | O.E_aterm ?t => 
    let (m, t) := reify_term m t in
    m, constr:(T.E_aterm $t)
  | O.E_abind ?a =>
    let (m, a) := reify_term m a in
    m, constr:(T.E_abind $a)
  | O.substitute ?t ?s =>
    let (m, t) := reify_term m t in
    let (m, s) := reify_subst m s in
    m, constr:(T.E_subst $t $s)
  | _ => make_mvar m t
  end
with reify_subst (m : map) (s : constr) : map * constr :=
  lazy_match! s with 
  | O.sid => m, constr:(T.E_sshift 0)
  | O.sshift ?k => m, constr:(T.E_sshift $k)
  | _ => make_mvar m s
  end.

Print sigT.

(** Build an [assignment] from a [map]. *)
Ltac2 rec build_assignment (m : map) : constr :=
  match m with 
  | [] => constr:(@nil (sigT denote_type))
  | (_idx, k, t) :: m => 
    let m' := build_assignment m in
    constr:(existT denote_type $k $t :: $m')
  end.

(** Reify a level one term in an empty map,
    returning the resulting assignment and reified term. *)
Ltac2 reify (t : constr) : constr * constr :=
  let (m, t) := reify_term [] t in
  let a := build_assignment m in 
  a, t.

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

Axiom t : O.expr O.Kt.

Ltac2 Eval reify constr:(
  O.E_ctor CApp
    (O.E_al_cons (O.E_aterm (O.substitute t (fun i => O.E_var i)))
    (O.E_al_cons (O.E_aterm t)
     O.E_al_nil))
).
  