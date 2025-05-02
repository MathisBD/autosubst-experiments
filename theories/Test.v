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
About seval_sreify_inv.*)

About term_ind'.