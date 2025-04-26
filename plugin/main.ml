open Monad
open Locally_nameless

(** Argument type. *)
type arg_ty = AT_base of EConstr.types | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor. *)
type signature = { ctor_names : string array; ctor_types : arg_ty list array }

(** Build the [EConstr.t] corresponding to an [arg_ty]. We use [ind] as a placeholder for
    the inductive type of terms. *)
let rec arg_ty_constr (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with AT_base b -> b | AT_term -> ind | AT_bind ty -> arg_ty_constr ty ind

(** Build the type of a constructor as a [EConstr.t]. We use [ind] as a placeholder for
    the inductive type of terms. *)
let ctor_ty_constr (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr ty ind) tys) ind

(** Rocq inductive [nat]. *)
let nat : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0)

(** Rocq inductive [string]. *)
let string : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Strings"; "String" ] "string", 0)

let ren : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "ren"

let up_ren : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "up_ren"

let declare_ind (s : signature) : Names.Ind.t m =
  (* Constructor names and types. We add an extra constructor for variables. *)
  let ctor_names = "Var" :: Array.to_list s.ctor_names in
  let ctor_types =
    (fun ind -> ret @@ arrow nat (EConstr.mkVar ind))
    :: Array.to_list
         (Array.map
            (fun ty ind -> ret @@ ctor_ty_constr ty (EConstr.mkVar ind))
            s.ctor_types)
  in
  (* Declare the inductive. *)
  declare_ind "term" EConstr.mkSet ctor_names ctor_types

let rec rename_arg (rename : EConstr.t) (r : EConstr.t) (arg : EConstr.t) (ty : arg_ty) :
    EConstr.t =
  match ty with
  | AT_base _ -> arg
  | AT_term -> apps rename [| r; arg |]
  | AT_bind ty -> rename_arg rename (app up_ren r) arg ty

let build_rename (ind : Names.Ind.t) (s : signature) : EConstr.t m =
  let open EConstr in
  (* Bind the input parameters. *)
  let* term = fresh_ind ind in
  fix "rename" 1 (arrows [ ren; term ] term) @@ fun rename ->
  lambda "r" ren @@ fun r ->
  lambda "t" term @@ fun t ->
  (* Build the case expression. *)
  case (mkVar t) @@ fun i args ->
  let* ctor = fresh_ctor (ind, i + 1) in
  if i = 0
  then
    (* Variable branch. *)
    ret @@ app ctor @@ app (mkVar r) (mkVar @@ List.hd args)
  else
    (* Other branches. *)
    let args' =
      List.map2
        (rename_arg (mkVar rename) (mkVar r))
        (List.map mkVar args)
        s.ctor_types.(i - 1)
    in
    ret @@ apps ctor @@ Array.of_list args'

let main () =
  let s =
    { ctor_names = [| "App"; "Lam" |]
    ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base string; AT_bind AT_term ] |]
    }
  in
  let ind = monad_run @@ declare_ind s in
  let rename =
    monad_run
      begin
        let* func = build_rename ind s in
        let* _ = typecheck func in
        declare_def Decls.Definition "rename" func
      end
  in
  Log.printf "plugin done"
