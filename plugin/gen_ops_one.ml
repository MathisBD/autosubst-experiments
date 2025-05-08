open Prelude

module Make (P : sig
  val sign : signature
  val ops0 : ops_zero
end) =
struct
  (**************************************************************************************)
  (** *** Build the level one signature. *)
  (**************************************************************************************)

  (** Build the inductive [Inductive base := B0 | B1 | ...] which indexes base types. *)
  let build_base () : Names.Ind.t m =
    let names =
      List.init (Array.length P.sign.base_types) @@ fun i -> "B" ^ string_of_int i
    in
    let types =
      List.init (Array.length P.sign.base_types) @@ fun _ ind -> ret @@ EConstr.mkVar ind
    in
    declare_ind "base" EConstr.mkSet names types

  (** Build the function [eval_base : base -> Type]. *)
  let build_eval_base (base : Names.Ind.t) : EConstr.t m =
    lambda "b" (mkind base) @@ fun b ->
    case (EConstr.mkVar b) @@ fun i _ -> ret @@ EConstr.of_constr P.sign.base_types.(i)

  (** Build the inductive [Inductive ctor := CApp | CLam | ...] which indexes non-variable
      constructors. *)
  let build_ctor () : Names.Ind.t m =
    let names = List.init P.sign.n_ctors @@ fun i -> "C" ^ P.sign.ctor_names.(i) in
    let types = List.init P.sign.n_ctors @@ fun _ ind -> ret @@ EConstr.mkVar ind in
    declare_ind "ctor" EConstr.mkSet names types

  (** Helper function to make a Rocq list with elements [xs]. Each element must be of type
      [ty]. *)
  let rec mklist (ty : EConstr.t) (xs : EConstr.t list) : EConstr.t =
    match xs with
    | [] -> app (Lazy.force Consts.nil) ty
    | x :: xs -> apps (Lazy.force Consts.cons) [| ty; x; mklist ty xs |]

  (** Build the function [ctor_type : ctor -> list (@arg_ty base)]. *)
  let build_ctor_type (ctor : Names.Ind.t) (base : Names.Ind.t) : EConstr.t m =
    let rec on_arg_ty (ty : arg_ty) : EConstr.t =
      match ty with
      | AT_base i ->
          apps (Lazy.force Consts.at_base) [| mkind base; mkctor (base, i + 1) |]
      | AT_term -> apps (Lazy.force Consts.at_term) [| mkind base |]
      | AT_bind ty -> apps (Lazy.force Consts.at_bind) [| mkind base; on_arg_ty ty |]
    in
    lambda "c" (mkind ctor) @@ fun c ->
    case (EConstr.mkVar c) @@ fun i _ ->
    ret
    @@ mklist (app (Lazy.force Consts.arg_ty) (mkind base))
    @@ List.map on_arg_ty P.sign.ctor_types.(i)

  (** Declare module [S] which contains the signature. *)
  let build_module_S (base : Names.Ind.t) (eval_base : Names.Constant.t)
      (ctor : Names.Ind.t) (ctor_type : Names.Constant.t) :
      Names.ModPath.t * Libnames.qualid =
    let mod_S =
      Declaremods.start_module None (Names.Id.of_string_soft "S") []
        (Declaremods.Check [])
    in
    let _ =
      def "t" @@ ret
      @@ apps
           (Lazy.force Consts.build_signature)
           [| mkind base; mkconst eval_base; mkind ctor; mkconst ctor_type |]
    in
    let _ = Declaremods.end_module () in
    let qualid_S =
      match mod_S with
      | MPdot (MPfile path, lab) -> Libnames.make_qualid path @@ Names.Label.to_id lab
      | _ -> Log.error "gen_signature: unexpected module path for [S]."
    in
    (mod_S, qualid_S)
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the level one signature. *)
let generate (s : signature) (ops0 : ops_zero) : ops_one =
  let module M = Make (struct
    let sign = s
    let ops0 = ops0
  end) in
  (* Build the signature. *)
  let base = monad_run @@ M.build_base () in
  let eval_base = def "eval_base" @@ M.build_eval_base base in
  let ctor = monad_run @@ M.build_ctor () in
  let ctor_type = def "ctor_type" @@ M.build_ctor_type ctor base in
  let mod_S, qualid_S = M.build_module_S base eval_base ctor ctor_type in
  (* Declare [Module T := LevelTwoSimp.Make (S)]. *)
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
  let const name =
    Names.Constant.make1 @@ Names.KerName.make mod_O @@ Names.Label.make name
  in
  let expr =
    (Names.MutInd.make1 @@ Names.KerName.make mod_O @@ Names.Label.make "expr", 0)
  in
  { base
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
  ; subst = const "subst"
  ; esize = const "esize"
  ; inv_Kt = const "inv_Kt"
  ; inv_Kal_nil = const "inv_Kal_nil"
  ; inv_Kal_cons = const "inv_Kal_cons"
  ; inv_Ka_base = const "inv_Ka_base"
  ; inv_Ka_term = const "inv_Ka_term"
  ; inv_Ka_bind = const "inv_Ka_bind"
  ; rename = const "rename"
  ; rscomp = const "rscomp"
  ; srcomp = const "srcomp"
  ; scons = const "scons"
  ; sid = const "sid"
  ; sshift = const "sshift"
  ; up_subst = const "up_subst"
  ; substitute = const "substitute"
  ; scomp = const "scomp"
  }
