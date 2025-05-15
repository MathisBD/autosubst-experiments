From Prototype Require Import Prelude Sig LevelOne LevelTwo LevelTwoSimp LevelTwoClean.
From Ltac2 Require Import RedFlags Printf.

(*********************************************************************************)
(** *** Load the plugin. *)
(*********************************************************************************)

Declare ML Module "autosubst-experiments.plugin".

Ltac2 @external reify_term : constr -> constr * constr := "autosubst-experiments.plugin" "reify_term".
Ltac2 @external reify_subst : constr -> constr * constr := "autosubst-experiments.plugin" "reify_subst".
Ltac2 @external eval_term : constr -> constr * constr := "autosubst-experiments.plugin" "eval_term".
Ltac2 @external eval_subst : constr -> constr * constr := "autosubst-experiments.plugin" "eval_subst".

(*********************************************************************************)
(** *** Instantiate the generic level 1 and level 2 machinery. *)
(*********************************************************************************)

(** [Make (S)] creates modules: 
    - [T] with level two expressions/substitutions built on signature [S].
    - [O] with level one expressions/substitutions built on signature [S]. *)
Module Make (S : Sig).
Include LevelTwoClean.Make (S).

(** Reduction flags to unfold all simplification functions (LevelTwoSimp.v). *)
Ltac2 red_flags_simp () : RedFlags.t := 
  red_flags:(beta iota delta 
    [esimp ssimp esimp_functional ssimp_functional
     qsimp rsimp qsimp_functional rsimp_functional
     substitute scomp substitute_functional scomp_functional
     rename srcomp rename_functional srcomp_functional
     tnat sren tnat_functional sren_functional
     substitute_aux scomp_aux sapply_aux sup rup 
     sapply rscomp sapply_functional rscomp_functional
     rapply rcomp rapply_functional rcomp_functional
     rcomp_aux rapply_aux rcons scons]).

(** Reduction flags to unfold all cleanup functions (LevelTwoClean.v). *)
Ltac2 red_flags_clean () : RedFlags.t :=
  red_flags:(beta iota delta 
    [eclean sclean eclean_functional sclean_functional
     qclean rclean qclean_functional rclean_functional
     eclean_ren eclean_subst eclean_subst_clause_1
     qclean_rapply qclean_rapply_clause_1
     dest_rshift dest_rshift_clause_2 dest_rshift_clause_2_clause_1
     mk_qsucc dest_var
     dest_ren dest_ren_clause_3 dest_ren_clause_3_clause_1 
     dest_ren_clause_4 dest_ren_clause_4_clause_1
     ]).

(** Reduction flags to unfold all (level 2 -> level 1) evaluation 
    functions (LevelTwo.v). *)
Ltac2 red_flags_eval () : RedFlags.t :=
  red_flags:(beta iota delta   
    [eeval seval eeval_functional seval_functional
     reval qeval reval_functional qeval_functional
     assign_qnat assign_ren assign_term assign_subst
     List.nth (* TODO use something else than [Lisnth]. *)
     ]).

End Make.

(*********************************************************************************)
(** *** [rasimpl]. *)
(*********************************************************************************)

(** [Simplification x y] expresses the fact that [x] simplifies into [y].
    Typically [x] is a ground term and [y] is an evar, and a proof of 
    [Simplification x y] instantiates [y] with a simplified version of [x]. *)
Class Simplification T (x y : T) := 
  MkSimplification { simplification : x = y }.
