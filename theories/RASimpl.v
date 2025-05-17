From Prototype Require Import Prelude Sig Constants.
From Prototype Require LevelOne LevelTwo LevelTwoClean LevelTwoSimp.
From Ltac2 Require Import RedFlags Printf.

Module O := LevelOne.
Module T := LevelTwo.
Module Simp := LevelTwoSimp.
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
Ltac2 red_flags_simp () : RedFlags.t := 
  red_flags:(beta iota delta 
    [T.eq_qnat T.eq_ren T.eq_qnat_functional T.eq_ren_functional
     Simp.dest_rspecial
     Simp.rcons Simp.rcons_clause_2 Simp.rcons_clause_2_1 Simp.rcons_clause_2_2
     Simp.rcons_clause_2_3 Simp.rcons_clause_2_4 Simp.rcons_clause_2_5
     Simp.rcons_clause_2_6 
     Simp.rapply_aux Simp.rcomp_aux 
     Simp.rapply Simp.rcomp Simp.rapply_functional Simp.rcomp_functional 
     Simp.qsimp Simp.rsimp Simp.qsimp_functional Simp.rsimp_functional
     Simp.scons Simp.ctail Simp.capply_zero
     Simp.ccomp_aux Simp.ccomp Simp.cup
     Simp.csubstitute_aux Simp.sccomp_aux
     Simp.csubstitute Simp.sccomp Simp.csubstitute_functional Simp.sccomp_functional
     Simp.sup  
     Simp.substitute Simp.scomp Simp.substitute_functional Simp.scomp_functional
     Simp.tvar Simp.sren Simp.tvar_functional Simp.sren_functional
     Simp.esimp Simp.ssimp Simp.esimp_functional Simp.ssimp_functional
     Nat.eqb
     ]).
     
(** Reduction flags to unfold all cleanup functions (LevelTwoClean.v). *)
Ltac2 red_flags_clean () : RedFlags.t :=
  red_flags:(beta iota delta 
    [Clean.eclean Clean.sclean Clean.eclean_functional Clean.sclean_functional
     Clean.qclean Clean.rclean Clean.qclean_functional Clean.rclean_functional
     Clean.rename Clean.substitute Clean.substitute_clause_1
     Clean.rapply Clean.rapply_clause_1
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
