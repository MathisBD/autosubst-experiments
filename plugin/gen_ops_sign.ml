open Prelude
open Signature
module C = Constants

module Make (P : sig
  val sign : signature
  val ops_conc : ops_concrete
end) =
struct
  (**************************************************************************************)
  (** *** Build the signature. *)
  (**************************************************************************************)

  (** Build the inductive [Inductive base := B0 | B1 | ...] which indexes base types. *)
  let build_base () : Names.Ind.t m =
    let names =
      List.init (Array.length P.sign.base_types) @@ fun i ->
      Names.Id.of_string_soft ("B" ^ string_of_int i)
    in
    let types =
      List.init (Array.length P.sign.base_types) @@ fun _ ind -> ret @@ EConstr.mkVar ind
    in
    declare_ind (Names.Id.of_string_soft "base") EConstr.mkSet names types

  (** Build the function [eval_base : base -> Type]. *)
  let build_eval_base (base : Names.Ind.t) : EConstr.t m =
    lambda "b" (mkind base) @@ fun b ->
    (* If there are no base types, Rocq can't infer the return type of the pattern match. *)
    let return _ _ : EConstr.t m =
      if Array.length P.sign.base_types = 0 then ret EConstr.mkSet else fresh_evar None
    in
    case (EConstr.mkVar b) ~return @@ fun i _ -> ret P.sign.base_types.(i)

  (** Build the inductive [Inductive fctor := Foption | Flist | ...] which indexes
      functors. *)
  let build_fctor () : Names.Ind.t m =
    let names =
      List.init (Array.length P.sign.functors) @@ fun i ->
      Names.Id.of_string_soft ("F" ^ string_of_int i)
    in
    let types =
      List.init (Array.length P.sign.functors) @@ fun _ ind -> ret @@ EConstr.mkVar ind
    in
    declare_ind (Names.Id.of_string_soft "fctor") EConstr.mkSet names types

  (** Build the function [fctor_shape : fctor -> Type]. *)
  let build_fctor_shape (fctor : Names.Ind.t) : EConstr.t m =
    lambda "f" (mkind fctor) @@ fun f ->
    case (EConstr.mkVar f) @@ fun i _ ->
    let* inst = fresh_evar None in
    ret @@ apps (mkglob' C.NF.shape) [| mkglob P.sign.functors.(i); inst |]

  (** Build the function [fctor_size : forall f : fctor, fctor_shape f -> nat]. *)
  let build_fctor_size (fctor : Names.Ind.t) (fctor_shape : Names.Constant.t) :
      EConstr.t m =
    lambda "f" (mkind fctor) @@ fun f ->
    let return _ f0 : EConstr.t m =
      ret @@ arrow (app (mkconst fctor_shape) (EConstr.mkVar f0)) (mkglob' C.nat)
    in
    case (EConstr.mkVar f) ~return @@ fun i _ ->
    let* inst = fresh_evar None in
    ret @@ apps (mkglob' C.NF.size) [| mkglob P.sign.functors.(i); inst |]

  (** Build the inductive [Inductive ctor := CApp | CLam | ...] which indexes non-variable
      constructors. *)
  let build_ctor () : Names.Ind.t m =
    let names =
      List.init P.sign.n_ctors @@ fun i ->
      Names.Id.of_string_soft ("C" ^ Names.Id.to_string P.sign.ctor_names.(i))
    in
    let types = List.init P.sign.n_ctors @@ fun _ ind -> ret @@ EConstr.mkVar ind in
    declare_ind (Names.Id.of_string_soft "ctor") EConstr.mkSet names types

  (** Helper function to make a Rocq list with elements [xs]. Each element must be of type
      [ty]. *)
  let rec mklist (ty : EConstr.t) (xs : EConstr.t list) : EConstr.t =
    match xs with
    | [] -> app (mkglob' C.nil) ty
    | x :: xs -> apps (mkglob' C.cons) [| ty; x; mklist ty xs |]

  (** Build the function [ctor_type : ctor -> list (@arg_ty base fctor)]. *)
  let build_ctor_type (ctor : Names.Ind.t) (base : Names.Ind.t) (fctor : Names.Ind.t) :
      EConstr.t m =
    let rec on_arg_ty (ty : arg_ty) : EConstr.t =
      match ty with
      | AT_base i ->
          apps (mkglob' C.at_base) [| mkind base; mkind fctor; mkctor (base, i + 1) |]
      | AT_term -> apps (mkglob' C.at_term) [| mkind base; mkind fctor |]
      | AT_bind ty -> apps (mkglob' C.at_bind) [| mkind base; mkind fctor; on_arg_ty ty |]
      | AT_fctor (i, ty) ->
          apps (mkglob' C.at_fctor)
            [| mkind base; mkind fctor; mkctor (fctor, i + 1); on_arg_ty ty |]
    in
    lambda "c" (mkind ctor) @@ fun c ->
    (* When [ctor] is empty, Rocq can't infer the return type of the pattern match. *)
    let return _ _ : EConstr.t m =
      ret @@ app (mkglob' C.list) @@ apps (mkglob' C.arg_ty) [| mkind base; mkind fctor |]
    in
    case (EConstr.mkVar c) ~return @@ fun i _ ->
    ret
    @@ mklist (apps (mkglob' C.arg_ty) [| mkind base; mkind fctor |])
    @@ List.map on_arg_ty P.sign.ctor_types.(i)
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Derive [EqDec] for an inductive using the Equations plugin, assuming no obligations
    remain. Only works for non-mutual inductives. *)
let derive_eqdec (ind : Names.Ind.t) : Names.Constant.t =
  (* Derive [NoConfusion] (required by [EqDec]) and [EqDec]. *)
  let pm =
    Ederive.derive ~pm:Declare.OblState.empty ~poly:false [ "NoConfusion"; "EqDec" ]
      [ Loc.tag @@ Names.GlobRef.IndRef ind ]
  in
  (* Check no obligations remain. *)
  Declare.Obls.check_solved_obligations ~pm ~what_for:(Pp.str "autosubst derive_eqdec");
  (* Get the name of the generated [EqDec] instance. *)
  let modpath = Names.Ind.modpath ind in
  let label =
    Names.Label.make (Names.Label.to_string (Names.MutInd.label (fst ind)) ^ "_EqDec")
  in
  Names.Constant.make1 @@ Names.KerName.make modpath label

(** Generate the level one signature. *)
let generate (sign : signature) (ops_conc : ops_concrete) : ops_sign =
  let module M = Make (struct
    let sign = sign
    let ops_conc = ops_conc
  end) in
  (* Build the signature. *)
  let base = monad_run @@ M.build_base () in
  let base_eqdec = derive_eqdec base in
  let eval_base = def "eval_base" @@ M.build_eval_base base in
  let fctor = monad_run @@ M.build_fctor () in
  let fctor_eqdec = derive_eqdec fctor in
  let fctor_shape = def "fctor_shape" @@ M.build_fctor_shape fctor in
  let fctor_size = def "fctor_size" @@ M.build_fctor_size fctor fctor_shape in
  let ctor = monad_run @@ M.build_ctor () in
  let ctor_eqdec = derive_eqdec ctor in
  let ctor_type = def "ctor_type" @@ M.build_ctor_type ctor base fctor in
  let sign =
    def "sign" @@ ret
    @@ apps (mkglob' C.build_signature)
         [| mkind base
          ; mkconst base_eqdec
          ; mkconst eval_base
          ; mkind fctor
          ; mkconst fctor_eqdec
          ; mkconst fctor_shape
          ; mkconst fctor_size
          ; mkind ctor
          ; mkconst ctor_eqdec
          ; mkconst ctor_type
         |]
  in
  (* Assemble everything. *)
  { base
  ; base_eqdec
  ; eval_base
  ; fctor
  ; fctor_eqdec
  ; fctor_shape
  ; fctor_size
  ; ctor
  ; ctor_eqdec
  ; ctor_type
  ; sign
  }
