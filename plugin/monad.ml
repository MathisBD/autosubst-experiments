type 'a m = Environ.env -> Evd.evar_map -> Evd.evar_map * 'a

let ret (x : 'a) : 'a m = fun env sigma -> (sigma, x)

let ( let* ) (mx : 'a m) (mf : 'a -> 'b m) : 'b m =
 fun env sigma ->
  let sigma, x = mx env sigma in
  mf x env sigma

let monad_run (mx : 'a m) : 'a =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let _, x = mx env sigma in
  x

let get_env : Environ.env m = fun env sigma -> (sigma, env)
let with_env env mx = fun _ sigma -> mx env sigma
let with_env' f mx = fun env sigma -> mx (f env) sigma
let get_sigma : Evd.evar_map m = fun env sigma -> (sigma, sigma)
let set_sigma sigma : unit m = fun env _ -> (sigma, ())
let modify_sigma f : unit m = fun env sigma -> (f sigma, ())
