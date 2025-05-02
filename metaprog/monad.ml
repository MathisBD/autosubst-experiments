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

let monad_ignore (mx : 'a m) : unit m =
  let* _ = mx in
  ret ()

module List = struct
  include Stdlib.List

  let rec monad_map (f : 'a -> 'b m) (xs : 'a list) : 'b list m =
    match xs with
    | [] -> ret []
    | x :: xs ->
        let* x' = f x in
        let* xs' = monad_map f xs in
        ret (x' :: xs')

  let monad_mapi (f : int -> 'a -> 'b m) (xs : 'a list) : 'b list m =
    let rec loop i xs =
      match xs with
      | [] -> ret []
      | x :: xs ->
          let* x' = f i x in
          let* xs' = loop (i + 1) xs in
          ret (x' :: xs')
    in
    loop 0 xs
end
