From Prototype Require Import Prelude Sig Constants.
From Prototype Require LevelOne LevelTwo LevelTwoClean.
From Ltac2 Require Import RedFlags Printf.

Module O := LevelOne.
Module T := LevelTwo.
Module Clean := LevelTwoClean.

(*********************************************************************************)
(** *** Load the plugin. *)
(*********************************************************************************)

Declare ML Module "autosubst-experiments.plugin".

Ltac2 @external reify_term : constr -> constr * constr := "autosubst-experiments.plugin" "reify_term".
Ltac2 @external reify_subst : constr -> constr * constr := "autosubst-experiments.plugin" "reify_subst".
Ltac2 @external eval_term : constr -> constr * constr := "autosubst-experiments.plugin" "eval_term".
Ltac2 @external eval_subst : constr -> constr * constr := "autosubst-experiments.plugin" "eval_subst".

(*********************************************************************************)
(** *** Reduction flags. *)
(*********************************************************************************)

(** Reduction flags to unfold all simplification functions (LevelTwoSimp.v). *)
(*Ltac2 red_flags_simp () : RedFlags.t := 
  red_flags:(beta iota delta 
    [esimp ssimp esimp_functional ssimp_functional
     qsimp rsimp qsimp_functional rsimp_functional
     substitute scomp substitute_functional scomp_functional
     rename srcomp rename_functional srcomp_functional
     tnat sren tnat_functional sren_functional
     substitute_aux scomp_aux sapply_aux sup rup 
     sapply rscomp sapply_functional rscomp_functional
     rapply rcomp rapply_functional rcomp_functional
     rcomp_aux rapply_aux rcons scons]).*)

(** Reduction flags to unfold all cleanup functions (LevelTwoClean.v). *)
Ltac2 red_flags_clean () : RedFlags.t :=
  red_flags:(beta iota delta 
    [Clean.eclean Clean.sclean Clean.eclean_functional Clean.sclean_functional
     Clean.qclean Clean.rclean Clean.qclean_functional Clean.rclean_functional
     Clean.clean_rename Clean.clean_substitute Clean.clean_substitute_clause_1
     Clean.clean_rapply Clean.clean_rapply_clause_1
     Clean.dest_rshift Clean.dest_rshift_clause_2 Clean.dest_rshift_clause_2_clause_1
     Clean.mk_qsucc Clean.dest_var
     Clean.dest_ren Clean.dest_ren_clause_3 Clean.dest_ren_clause_3_clause_1 
     Clean.dest_ren_clause_4 Clean.dest_ren_clause_4_clause_1
     Clean.nat_add
     ]).

(** Reduction flags to unfold all (level 2 -> level 1) evaluation 
    functions (LevelTwo.v). *)
Ltac2 red_flags_eval () : RedFlags.t :=
  red_flags:(beta iota delta   
    [T.eeval T.seval T.eeval_functional T.seval_functional
     T.reval T.qeval T.reval_functional T.qeval_functional
     T.assign_qnat T.assign_ren T.assign_term T.assign_subst
     T.list_nth
     ]).

(*********************************************************************************)
(** *** [rasimpl]. *)
(*********************************************************************************)

(** [Simplification x y] expresses the fact that [x] simplifies into [y].
    Typically [x] is a ground term and [y] is an evar, and a proof of 
    [Simplification x y] instantiates [y] with a simplified version of [x]. *)
Class Simplification T (x y : T) := 
  MkSimplification { simplification : x = y }.
