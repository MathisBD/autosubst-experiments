open Prelude
module C = Constants

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
    | [] -> app (mkglob' C.nil) ty
    | x :: xs -> apps (mkglob' C.cons) [| ty; x; mklist ty xs |]

  (** Build the function [ctor_type : ctor -> list (@arg_ty base)]. *)
  let build_ctor_type (ctor : Names.Ind.t) (base : Names.Ind.t) : EConstr.t m =
    let rec on_arg_ty (ty : arg_ty) : EConstr.t =
      match ty with
      | AT_base i -> apps (mkglob' C.at_base) [| mkind base; mkctor (base, i + 1) |]
      | AT_term -> apps (mkglob' C.at_term) [| mkind base |]
      | AT_bind ty -> apps (mkglob' C.at_bind) [| mkind base; on_arg_ty ty |]
    in
    lambda "c" (mkind ctor) @@ fun c ->
    case (EConstr.mkVar c) @@ fun i _ ->
    ret
    @@ mklist (app (mkglob' C.arg_ty) (mkind base))
    @@ List.map on_arg_ty P.sign.ctor_types.(i)

  (** Build the signature. *)
  let build_signature (base : Names.Ind.t) (eval_base : Names.Constant.t)
      (ctor : Names.Ind.t) (ctor_type : Names.Constant.t) : EConstr.t m =
    ret
    @@ apps (mkglob' C.build_signature)
         [| mkind base; mkconst eval_base; mkind ctor; mkconst ctor_type |]
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
  let sign = def "signature" @@ M.build_signature base eval_base ctor ctor_type in
  (* Assemble everything. *)
  { base; eval_base; ctor; ctor_type; sign }
