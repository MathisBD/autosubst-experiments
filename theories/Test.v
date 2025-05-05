From Coq Require Import Lia.
From Coq Require Import String.
From Prototype Require Import Prelude Sig.
From Prototype Require Constants LevelOne LevelTwo LevelTwoIrred LevelTwoSimp.

Declare ML Module "autosubst-experiments.plugin".

Test.

(*Print term.
Print rename.
Print subst.
Print srcomp.
Print rscomp.
Print sid.
Print sshift.
Print scons.
Print up_subst.
Print substitute.
Print scomp.*)

(*About congr_App.
About congr_Lam.
About congr_rename.
About congr_rscomp.
About congr_srcomp.
About congr_scons.
About congr_up_subst.
About congr_substitute.
About congr_scomp.*)

(*Print base.
Print eval_base.
Print ctor.
Print ctor_type.
Print S.t.
About T.*)

(*Print reify.
Print sreify.
Print eval_arg.
Print eval_args.
Print eval_kind.
Print eval_ctor.
Print eval.*)

(*About eval_reify_inv.
About seval_sreify_inv.
About term_ind'.*)

About eval_rename.
About seval_rscomp.
About seval_srcomp.
About seval_scons.
About seval_up_subst.

Lemma eval_substitute (s : T.O.subst) (t : T.O.expr Kt) : 
  eval Kt (T.O.substitute s t) = substitute (seval s) (eval Kt t).
Proof.
revert s. pattern t. apply term_ind' ; clear t.
- intros i s. reflexivity.
- intros t1 IH1 t2 IH2 s. repeat (simp substitute ; simpl). 
  apply congr_App.
  + rewrite IH1. reflexivity.
  + rewrite IH2. reflexivity. 
- intros str t IH s. repeat (simp substitute ; simpl). 
  apply congr_Lam.
  + reflexivity.
  + rewrite IH. apply congr_substitute ; [|reflexivity].
    repeat (rewrite seval_up_subst ; apply congr_up_subst).
    reflexivity.
Qed.


(*Lemma eval_rename (r : ren) (t : T.O.expr Kt) :
  eval Kt (T.O.rename r t) = rename r (eval Kt t).
Proof.
revert r. pattern t. apply term_ind'.
- intros i r. reflexivity.
- intros t1 IH1 t2 IH2 r. apply congr_App ; auto. 
- intros str t1 IH1 r. apply congr_Lam ; auto. 
Qed.*)
