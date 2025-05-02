module PVMonad = struct
  let ( >> ) = Proofview.Monad.( >> )
  let ( >>= ) = Proofview.Monad.( >>= )
  let ret = Proofview.Monad.return
  let ( let* ) = Proofview.Monad.( >>= )
end

let intro_n (n : int) : unit Proofview.tactic =
  Tactics.intro_patterns false @@ List.init n
  @@ fun _ ->
  CAst.make @@ Tactypes.IntroNaming (Namegen.IntroFresh (Names.Id.of_string_soft "x"))

let intro_fresh (x : string) : Names.Id.t Proofview.tactic =
  let open PVMonad in
  Proofview.Goal.enter_one @@ fun g ->
  let idset =
    Environ.ids_of_named_context_val @@ Environ.named_context_val @@ Proofview.Goal.env g
  in
  let id = Namegen.next_ident_away (Names.Id.of_string_soft x) idset in
  let* _ = Tactics.intro_mustbe_force id in
  ret id

let intro_rewrite ~(dir : bool) : unit Proofview.tactic =
  let pattern = CAst.make @@ Tactypes.IntroAction (Tactypes.IntroRewrite dir) in
  Tactics.intro_patterns false [ pattern ]

let print_open_goals : unit Proofview.tactic =
  Proofview.Goal.enter @@ fun goal ->
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  let concl = Proofview.Goal.concl goal in
  Format.ksprintf
    (fun res -> Feedback.msg_notice (Pp.str res))
    "open goal: \n%s |- %s"
    (Pp.string_of_ppcmds @@ Printer.pr_named_context_of env sigma)
    (Pp.string_of_ppcmds @@ Printer.pr_econstr_env env sigma concl);
  Proofview.tclUNIT ()

let dispatch (tac : int -> unit Proofview.tactic) : unit Proofview.tactic =
  let open PVMonad in
  let* n = Proofview.numgoals in
  Proofview.tclDISPATCH @@ List.init n tac

let auto ?(depth : int option) ?(lemmas : EConstr.t list option) () :
    unit Proofview.tactic =
  let lemmas =
    match lemmas with
    | None -> []
    | Some ts -> List.map (fun t env sigma -> (sigma, t)) ts
  in
  Auto.gen_auto depth lemmas (Some [ "core" ])

let rewrite ~(dir : bool) (eq : Names.GlobRef.t) : unit Proofview.tactic =
  let delayed_eq =
   fun env sigma ->
    let sigma, t = Evd.fresh_global env sigma eq in
    (sigma, (t, Tactypes.NoBindings))
  in
  Rewrite.cl_rewrite_clause delayed_eq dir Locus.AllOccurrences None

let rec repeat_n (n : int) (tac : 'a Proofview.tactic) : 'a list Proofview.tactic =
  let open PVMonad in
  if n <= 0
  then ret []
  else
    let* x = tac in
    let* xs = repeat_n (n - 1) tac in
    ret (x :: xs)

let pattern (t : EConstr.t) : unit Proofview.tactic =
  Tactics.pattern_option [ (Locus.AllOccurrences, t) ] None
