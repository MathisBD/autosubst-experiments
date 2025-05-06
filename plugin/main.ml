open Prelude

(** Main entry point for the plugin. *)
let main () =
  let s =
    { n_ctors = 2
    ; base_types = [| EConstr.to_constr Evd.empty @@ Lazy.force Consts.string |]
    ; ctor_names = [| "App"; "Lam" |]
    ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base 0; AT_bind AT_term ] |]
    }
  in
  (*let term n = List.init n @@ fun _ -> AT_term in
  let s =
    { n_ctors = 16
    ; base_types =
        [| EConstr.to_constr Evd.empty @@ Lazy.force Consts.nat
         ; EConstr.to_constr Evd.empty @@ Lazy.force Consts.string
        |]
    ; ctor_names =
        [| "csort"
         ; "cpi"
         ; "clam"
         ; "capp"
         ; "cunit"
         ; "ctt"
         ; "ctop"
         ; "cstar"
         ; "cbot"
         ; "cbot_elim"
         ; "pvec"
         ; "pvnil"
         ; "pvcons"
         ; "pvec_elim"
         ; "pvec_elimG"
         ; "pvec_elimP"
        |]
    ; ctor_types =
        [| [ AT_base 0; AT_base 1 ]
         ; [ AT_base 0; AT_term; AT_bind AT_term ]
         ; [ AT_base 0; AT_term; AT_bind AT_term ]
         ; term 2
         ; []
         ; []
         ; []
         ; []
         ; []
         ; AT_base 1 :: term 2
         ; term 4
         ; term 1
         ; term 3
         ; term 12
         ; term 12
         ; term 10
        |]
    }
  in*)
  (* Level zero operations. *)
  let module Ops_zero = Gen_ops_zero.Make (struct
    let sign = s
  end) in
  let ops0 = Ops_zero.generate () in
  (* Level one operations. *)
  let module Ops_one = Gen_ops_one.Make (struct
    let sign = s
    let ops0 = ops0
  end) in
  let ops1 = Ops_one.generate () in
  (* Reification and evaluation functions. *)
  let module Ops_reify_eval = Gen_ops_reify_eval.Make (struct
    let sign = s
    let ops0 = ops0
    let ops1 = ops1
  end) in
  let re = Ops_reify_eval.generate () in
  (* Congruence lemmas. *)
  let module Ops_congr = Gen_ops_congr.Make (struct
    let sign = s
    let ops0 = ops0
  end) in
  let congr = Ops_congr.generate () in
  (* Bijection lemmas. *)
  let module Ops_bijection = Gen_ops_bijection.Make (struct
    let sign = s
    let ops0 = ops0
    let ops1 = ops1
    let congr = congr
    let re = re
  end) in
  let bij = Ops_bijection.generate () in
  (* Push-eval lemmas. *)
  let module Ops_push_eval = Gen_ops_push_eval.Make (struct
    let sign = s
    let ops0 = ops0
    let ops1 = ops1
    let congr = congr
    let re = re
    let bij = bij
  end) in
  let _ = Ops_push_eval.generate () in
  ()
