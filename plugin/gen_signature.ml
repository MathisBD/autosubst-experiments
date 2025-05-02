open Prelude

(**************************************************************************************)
(** *** Build the level one signature. *)
(**************************************************************************************)

(** Build the inductive [Inductive base := B0 | B1 | ...] which indexes base types. *)
let build_base (sign : signature) : Names.Ind.t m =
  let names =
    List.init (Array.length sign.base_types) @@ fun i -> "B" ^ string_of_int i
  in
  let types =
    List.init (Array.length sign.base_types) @@ fun _ ind -> ret @@ EConstr.mkVar ind
  in
  declare_ind "base" EConstr.mkSet names types

(** Build the function [eval_base : base -> Type]. *)
let build_eval_base (sign : signature) (base : Names.Ind.t) : EConstr.t m =
  lambda "b" (mkind base) @@ fun b ->
  case (EConstr.mkVar b) @@ fun i _ -> ret @@ EConstr.of_constr sign.base_types.(i)

(** Build the inductive [Inductive ctor := CApp | CLam | ...] which indexes non-variable
    constructors. *)
let build_ctor (sign : signature) : Names.Ind.t m =
  let names = List.init sign.n_ctors @@ fun i -> "C" ^ sign.ctor_names.(i) in
  let types = List.init sign.n_ctors @@ fun _ ind -> ret @@ EConstr.mkVar ind in
  declare_ind "ctor" EConstr.mkSet names types

let rec mklist (ty : EConstr.t) (xs : EConstr.t list) : EConstr.t =
  match xs with
  | [] -> app (Lazy.force Consts.nil) ty
  | x :: xs -> apps (Lazy.force Consts.cons) [| ty; x; mklist ty xs |]

(** Build the function [ctor_type : ctor -> list (@arg_ty base)]. *)
let build_ctor_type (sign : signature) (ctor : Names.Ind.t) (base : Names.Ind.t) :
    EConstr.t m =
  let rec on_arg_ty (ty : arg_ty) : EConstr.t =
    match ty with
    | AT_base i -> apps (Lazy.force Consts.at_base) [| mkind base; mkctor (base, i + 1) |]
    | AT_term -> apps (Lazy.force Consts.at_term) [| mkind base |]
    | AT_bind ty -> apps (Lazy.force Consts.at_bind) [| mkind base; on_arg_ty ty |]
  in
  lambda "c" (mkind ctor) @@ fun c ->
  case (EConstr.mkVar c) @@ fun i _ ->
  ret
  @@ mklist (app (Lazy.force Consts.arg_ty) (mkind base))
  @@ List.map on_arg_ty sign.ctor_types.(i)

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the level one signature. *)
let generate (s : signature) (ops : ops_zero) : ops_one =
  (* Build the signature. *)
  let base = monad_run @@ build_base s in
  let eval_base = def "eval_base" @@ build_eval_base s base in
  let ctor = monad_run @@ build_ctor s in
  let ctor_type = def "ctor_type" @@ build_ctor_type s ctor base in
  (* Declare module [S] which contains the signature. *)
  let _ =
    Declaremods.start_module None (Names.Id.of_string_soft "S") [] (Declaremods.Check [])
  in
  let sign =
    def "t" @@ ret
    @@ apps
         (Lazy.force Consts.build_signature)
         [| mkind base; mkconst eval_base; mkind ctor; mkconst ctor_type |]
  in
  let _ = Declaremods.end_module () in
  (* Declare [Module T := LevelTwoSimp.Make (S)] and the shorthand [O := T.O]. *)
  let qualid_S = mk_qualid [ "Prototype"; "Test" ] "S" in
  let qualid_Make = mk_qualid [ "Prototype"; "LevelTwoSimp" ] "Make" in
  let mod_T =
    Declaremods.declare_module (Names.Id.of_string_soft "T") [] (Declaremods.Check [])
      [ ( CAst.make
          @@ Constrexpr.CMapply (CAst.make @@ Constrexpr.CMident qualid_Make, qualid_S)
        , Declaremods.DefaultInline )
      ]
  in
  let mod_O = Names.ModPath.MPdot (mod_T, Names.Label.make "O") in
  (* Build the names of level one constants. *)
  let expr =
    (Names.MutInd.make1 @@ Names.KerName.make mod_O @@ Names.Label.make "expr", 0)
  in
  { sign
  ; base
  ; eval_base
  ; ctor
  ; ctor_type
  ; expr
  ; e_var = (expr, 1)
  ; e_ctor = (expr, 2)
  ; e_al_nil = (expr, 3)
  ; e_al_cons = (expr, 4)
  ; e_abase = (expr, 5)
  ; e_aterm = (expr, 6)
  ; e_abind = (expr, 7)
  ; subst = Names.Constant.make1 @@ Names.KerName.make mod_O @@ Names.Label.make "subst"
  }
