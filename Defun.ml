(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module M = Map.Make(Atom)

let new_tag : unit -> int =
  let i = ref 0 in
  fun () -> incr i;
  !i

let applyname = Atom.fresh "apply"
let this = Atom.fresh "this"
let that = [Atom.fresh "that"; Atom.fresh "that"]
let apply_argc = List.length that

let fill_with_dummy_var (l: T.variable list) : T.variable list =
  let rec add_dummy l len =
    if len >= apply_argc then
      l
    else
      add_dummy ((Atom.fresh "dummy")::l) (len+1)
  in List.rev(add_dummy (List.rev l) (List.length l))

let fill_with_dummy_val (l: T.value list) : T.value list =
  let rec add_zero l len =
    if len >= 2 then
      l
    else
      add_zero ((T.VLit(0))::l) (len+1)
  in List.rev(add_zero (List.rev l) (List.length l))

let rec defun (t: S.term)
              (evar: S.value M.t)
              (efun: (int * Atom.Set.elt list) M.t)
              (apply: T.branch list) :
  T.term * (S.value M.t) * ((int * Atom.Set.elt list) M.t) * (T.branch list)
=
match t with
  | S.Exit -> T.Exit, evar, efun, apply
  | S.TailCall (v, args) -> begin
  match v with
    | S.VVar f -> T.TailCall(applyname,
                             (T.VVar(f)::(fill_with_dummy_val args))),
                  evar, efun, apply
    | _ -> assert false
  end
  | S.Print (v, tnext) ->
    let tdefun, evar, efun, apply = defun tnext evar efun apply in
    T.Print (v, tdefun), evar, efun, apply
  | S.Ifzero (vif, tthen, telse) ->
    let tthendefun, evar, efun, apply = defun tthen evar efun apply in
    let telsedefun, evar, efun, apply = defun telse evar efun apply in
    T.Ifzero(vif, tthendefun, telsedefun), evar, efun, apply
  | S.LetVal (var, v, exp) ->
    let evar = M.add var v evar in
    let expdefun, evar, efun, apply = defun exp evar efun apply in
    T.LetVal(var, v, expdefun), evar, efun, apply
  | S.LetBlo(var, (S.Lam(s, args, t_lam) as blk), exp) ->
    let fv = match s with
      | S.Self(self) -> self::(Atom.Set.elements (S.fv_block blk))
      | _ -> Atom.Set.elements (S.fv_block blk)
    in
    let evar = match s with
      | S.Self(self) -> List.fold_left
        (fun out arg -> M.add arg (T.VVar(arg)) out) evar (self::args)
      | _ -> List.fold_left
        (fun out arg -> M.add arg (T.VVar(arg)) out) evar args
    in
    let tag = new_tag() in
    let t, evar, efun, apply = defun t_lam evar efun apply in
    let t = List.fold_right2
      (fun arg that out -> T.LetVal(arg, T.VVar(that), out))
      (fill_with_dummy_var args) that t in
    let branch = T.Branch(tag, fv, t) in
    let efun = M.add var (tag, fv) efun in
    let evar = M.add var (T.VVar(var)) evar in
    let expdefun, evar, efun, apply = defun exp evar efun (branch::apply) in
    T.LetBlo(var, T.Con(tag, List.map (fun var -> T.VVar(var)) fv), expdefun),
      evar, efun, apply

let defun_term (t : S.term) : T.program =
  let prog, _, _, apply = defun t M.empty M.empty [] in
  let apply_fun = T.Fun(applyname, this::that, T.Swi(T.VVar(this), apply)) in
  T.Prog([apply_fun], prog)
