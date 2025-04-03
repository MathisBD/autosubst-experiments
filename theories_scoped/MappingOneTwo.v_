From Equations Require Import Equations.
From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo.

Module Make (S : Sig).
Module O := LevelOne.Make (S).
Module T := LevelTwo.Make (S).

(*********************************************************************************)
(** *** Denotation (level two -> level one). *)
(*********************************************************************************)

Definition denote_type (k : T.kind) (s : T.scope) : Type :=
  match k, s with 
  | T.K_s, T.S2 n m => O.subst n m
  | T.K_t, T.S1 n => O.term O.K_t n
  | T.K_al tys, T.S1 n => O.term (O.K_al tys) n
  | T.K_a ty, T.S1 n => O.term (O.K_a ty) n
  | _, _ => False
  end.
  
(** Helper lemma used to discard an impossible case in [denote]. *)
Lemma not_K_s_S1 {n} : T.term T.K_s (T.S1 n) -> False.
Proof. intros t ; dependent induction t ; eauto. Qed.
    
(** Mapping from level two terms/substitutions to level one terms/substitutions. *)
Fixpoint denote {k s} (t : T.term k s) {struct t} : denote_type k s :=
  match t in T.term k0 s0 return denote_type k0 s0 with
  | T.T_var i => O.T_var i 
  | T.T_ctor c args => O.T_ctor c (denote args)
  | @T.T_subst _ _ T.K_t t s => O.substitute (denote t) (denote s)
  | @T.T_subst _ _ (T.K_a ty) t s => O.substitute (denote t) (denote s)
  | @T.T_subst _ _ (T.K_al tys) t s => O.substitute (denote t) (denote s)
  | @T.T_subst _ _ T.K_s t s => not_K_s_S1 t
  
  | T.T_al_nil => O.T_al_nil
  | T.T_al_cons a args => O.T_al_cons (denote a) (denote args)
  
  | T.T_abase b x => O.T_abase b x
  | T.T_aterm t => O.T_aterm (denote t)
  | T.T_abind a => O.T_abind (denote a)

  | T.T_sshift k => O.sshift k
  | T.T_scons t s => O.scons (denote t) (denote s)
  | T.T_scomp s1 s2 => O.scomp (denote s1) (denote s2)
  end.

(*********************************************************************************)
(** *** Correctness of denotation. *)
(*********************************************************************************)

(** Equality on level one terms/substitutions. We use pointwise equality 
    for substitutions so as to not assume functional extensionality. *)
Definition denote_rel k s : relation (denote_type k s) :=
  match k, s with 
  | T.K_s, T.S2 n m => @point_eq (fin n) (O.term O.K_t m)
  | T.K_t, T.S1 n => eq
  | T.K_a _, T.S1 n => eq 
  | T.K_al _, T.S1 n => eq
  | _, _ => fun _ _ => True
  end.

#[global] Instance denote_rel_equiv k s : Equivalence (denote_rel k s).
Proof. 
constructor ; destruct k ; destruct s ; auto.
all: try (intros ????? ; etransitivity ; eauto).
- intros ?. reflexivity.
- intros ???. now symmetry.
Qed.

(** Main correctness result for [denote]: it transports level-two _sigma-equal_ terms 
    to level-one _equal_ terms. *)
#[global] Instance denote_proper {k s} : Proper (T.axiom_eq ==> denote_rel k s) (@denote k s).
Proof.
intros t1 t2 Ht. induction Ht ; simpl in * ; try auto.
- reflexivity.
- now symmetry.
- etransitivity ; eauto. 
- destruct k ; simpl ; auto.
  + now rewrite IHHt1, IHHt2.
  + now rewrite IHHt1, IHHt2.
  + now rewrite IHHt1, IHHt2.
- now rewrite IHHt1, IHHt2.
- now rewrite IHHt1, IHHt2.
- f_equal. apply O.substitute_proper ; auto.
  rewrite O.up_subst_alt. reflexivity.
- destruct k ; simpl ; solve [now setoid_rewrite O.subst_subst | auto].
- now setoid_rewrite <-O.sshift_succ_r.
- now setoid_rewrite O.sid_scons.
- now setoid_rewrite O.scomp_id_l.
- now setoid_rewrite O.scomp_id_r.
- now setoid_rewrite O.scomp_assoc.
- now setoid_rewrite O.scomp_scons_distrib.
Qed.

End Make.
