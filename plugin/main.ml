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
  let ops0 = Gen_operations.generate s in
  let congr = Gen_congr_lemmas.generate s ops0 in
  let ops1 = Gen_signature.generate s ops0 in
  let re = Gen_reify_eval.generate s ops0 ops1 in
  let _ = Gen_bijection.generate s ops0 ops1 congr re in
  ()
