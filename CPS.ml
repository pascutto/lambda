(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

let identity = Atom.fresh "identity"

type tailvalue =
  | Blk of T.block
  | Val of T.value

let rec subst_value (value : T.value) (v : T.value) (x : T.variable) : T.value =
match value with
  | T.VVar y when Atom.equal x y -> v
  | T.VBinOp (v1, op, v2) ->
    let v1' = subst_value v1 v x in
    let v2' = subst_value v2 v x in
    T.VBinOp(v1', op, v2')
  | _ -> value

and subst_term (t: T.term) (v: T.value) (x: T.variable) : T.term =
match t with
  | T.Exit -> T.Exit
  | T.TailCall (f, l) ->
    let f' = subst_value f v x in
    let l' = List.map (fun a -> subst_value a v x) l in
    T.TailCall(f', l')
  | T.Print (value, nxt) ->
    let value' = subst_value value v x in
    let nxt' = subst_term nxt v x in
    T.Print(value', nxt')
  | T.Ifzero (tif, tthen, telse) ->
    let tif' = subst_value tif v x in
    let tthen' = subst_term tthen v x in
    let telse' = subst_term telse v x in
    T.Ifzero (tif', tthen', telse')
  | T.LetVal (y, value, nxt) ->
    let value' = subst_value value v x in
    let nxt' = subst_term nxt v x in
    T.LetVal(y, value', nxt')
  | T.LetBlo(y, T.Lam (s, l, bdy), nxt) ->
    let nxt' = subst_term nxt v x in
    let bdy' = subst_term bdy v x in
    T.LetBlo(y, T.Lam(s, l, bdy'), nxt')

let tval_of_sval (v: S.term) : T.value =
match v with
  | S.Var x -> T.VVar x
  | S.Lit i -> T.VLit i
  | _ -> assert false

type continuation =
  | Object of T.value
  | Transformation of T.variable * T.term

let apply (c : continuation) (v : tailvalue): T.term =
match v with
  | Val tval -> begin
    match c with
      | Object w -> T.TailCall(w, [tval])
      | Transformation (x, t) -> subst_term t tval x
  end
  | Blk tblk -> begin
    match c with
    | Object w ->
      let f = Atom.fresh "block" in
      T.LetBlo(f, tblk, T.TailCall(w, [T.VVar(f)]))
    | Transformation (x, t) ->
      let f = Atom.fresh "block" in
      T.LetBlo(f, tblk, (subst_term t (T.VVar f) x))
  end

let reify (c : continuation) : tailvalue =
match c with
  | Object w -> Val w
  | Transformation (x, t) -> Blk(T.Lam(T.NoSelf, [x], t))

let rec cps_value(t : S.term) : tailvalue =
match t with
  | S.Var x -> Val(T.VVar x)
  | S.Lam (s, var, bdy) ->
    let k = Atom.fresh "k" in
    Blk(T.Lam(s, [var ; k], cps_lambda bdy (Object (T.VVar k))))
  | S.Lit i -> Val(T.VLit i)
  | _ -> assert false


and cps_lambda (t : S.term) (c : continuation) : T.term =
match t with
  | S.Var _ -> apply c (cps_value t)
  | S.Lam (_, _, _) -> apply c (cps_value t)
  | S.App (f, t) -> begin
    let x1 = Atom.fresh "app" in
    let x2 = Atom.fresh "app" in
    match reify c with
      | Val v ->
        cps_lambda f
          (Transformation(x1,
            cps_lambda t (Transformation(x2,
              T.TailCall(T.VVar(x1), [T.VVar(x2); v])))))
      | Blk b ->
        let nf = Atom.fresh "app" in
        cps_lambda f
          (Transformation(x1,
            cps_lambda t (Transformation(x2,
              T.LetBlo(nf, b,
                T.TailCall(T.VVar(x1), [T.VVar(x2); T.VVar(nf)]))))))
  end
  | S.Lit _ -> apply c (cps_value t)
  | S.BinOp (t1, op, t2) -> begin
    match t1 with
    | S.Var(_) | S.Lit(_) -> begin
      match t2 with
      | S.Var(_) |S.Lit(_) -> apply c (Val(T.VBinOp(tval_of_sval t1, op, tval_of_sval t2)))
      | _ ->
        let t2' = Atom.fresh "binop" in
        cps_lambda (S.Let(t2', t2, S.BinOp(t1, op, S.Var(t2')))) c
    end
    | _ -> begin
      let t1' = Atom.fresh "binop" in
      match t2 with
      | S.Var(_) |S.Lit(_) -> cps_lambda (S.Let(t1', t1, S.BinOp(S.Var(t1'), op, t2))) c
      | _ ->
        let t2' = Atom.fresh "binop" in
        cps_lambda (S.Let(t1', t1, S.Let(t2', t2, S.BinOp(S.Var(t1'), op, S.Var(t2'))))) c
    end
  end
  | S.Print te -> begin
    match te with
    | S.Var _ | S.Lit _ ->
      T.Print(tval_of_sval te, cps_lambda (S.App(S.Var(identity), te)) c)
    | _ ->
      let x = Atom.fresh "print" in
      cps_lambda (S.Let(x, te, S.Print(S.Var(x)))) c
  end
  | S.Ifzero (tif, tthen, telse) -> begin
  match tif with
    | S.Var _ | S.Lit _ ->
      T.Ifzero(tval_of_sval tif, cps_lambda tthen c, cps_lambda telse c)
    | _ ->
      let x = Atom.fresh "ifzero" in
      cps_lambda (S.Let(x, tif, S.Ifzero(S.Var(x), tthen, telse))) c
  end
  | S.Let (var, t1, t2) ->
    let x1 = Atom.fresh "let" in
    cps_lambda t1
      (Transformation(x1, T.LetVal(var, T.VVar(x1), (cps_lambda t2 c))))

let rec eliminate_variable (t: T.term) : T.term =
match t with
  | T.Exit -> t
  | T.TailCall (_, _) -> t
  | T.Print (value, nxt) ->
    let nxt' = eliminate_variable nxt in
    T.Print(value, nxt')
  | T.Ifzero (tif, tthen, telse) ->
    let tthen' = eliminate_variable tthen in
    let telse' = eliminate_variable telse in
    T.Ifzero (tif, tthen', telse')
  | T.LetVal (y, value, nxt) -> begin
      match value with
      | T.VVar _ -> (*eliminate_variable*)(subst_term nxt value y)
      | _ -> eliminate_variable nxt
    end
  | T.LetBlo(y, T.Lam (s, l, bdy), nxt) ->
    let nxt' = eliminate_variable nxt in
    let bdy' = eliminate_variable bdy in
    T.LetBlo(y, T.Lam(s, l, bdy'), nxt')

let cps_term (t : S.term) : T.term =
  let xId = Atom.fresh "x" in
  let exit = Atom.fresh "exit" in
  let x = Atom.fresh "main" in
  eliminate_variable (T.LetBlo(
    exit,
    T.Lam(T.NoSelf, [x], T.Exit),
    cps_lambda (
      S.Let(identity, S.Lam(S.NoSelf, xId, S.Var(xId)), t))
      (Object(T.VVar(exit)))))
