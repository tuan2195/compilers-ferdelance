open Printf
open Types
open Expr
open Instruction

type 'a envt = (string * 'a) list

let rec is_anf (e : 'a expr) : bool =
match e with
    | EPrim1(_, e, _) -> is_imm e
    | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
    | ELet(binds, body, _) -> List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
    | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
    | ETuple(expr_ls, _) -> List.for_all is_anf expr_ls
    | EGetItem(tup, idx, _) -> is_anf tup && is_imm idx
    | _ -> is_imm e
and is_imm e =
    match e with
    | ENumber _ -> true
    | EBool _ -> true
    | EId _ -> true
    | _ -> false
;;

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

let rec print_env e cmt =
    match e with
    | [] -> ()
    | (x, _)::rest -> printf "%s: %s\n" cmt x; print_env rest cmt

let well_formed p =
let rec wf_E e (env : sourcespan envt) =
    let rec dupe x binds =
        match binds with
        | [] -> None
        | (y, _, pos)::_ when x = y -> Some pos
        | _::rest -> dupe x rest in
    match e with
    | ELet(binds, body, _) ->
        let rec process_binds rem_binds env =
            match rem_binds with
            | [] -> (env, [])
            | (x, e, pos)::rest ->
                let shadow = match dupe x rest with
                    | Some where -> [DuplicateId(x, where, pos)]
                    | None ->
                        try let existing = List.assoc x env in
                            [ShadowId(x, pos, existing)]
                        with Not_found -> [] in
                let errs_e = wf_E e env  in
                let new_env = (x, pos)::env in
                let (newer_env, errs) = process_binds rest new_env in
                (newer_env, (shadow @ errs_e @ errs)) in
        let (env2, errs) = process_binds binds env in
        errs @ wf_E body env2
    | ELetRec(binds, body, _) ->
        let rec build_env b =
            match b with
            | [] -> []
            | (x, _, pos)::rest -> (x, pos)::build_env rest in
        let new_env = env @ build_env binds in
        let rec process_binds rem_binds =
            match rem_binds with
            | [] -> []
            | (x, e, pos)::rest ->
                match e with
                | ELambda _ ->
                    let shadow = match dupe x rest with
                        | Some where -> [DuplicateFun(x, where, pos)]
                        | None ->
                            try let existing = List.assoc x env in
                                [ShadowId(x, pos, existing)]
                            with Not_found -> [] in
                    let errs_e = wf_E e new_env in
                    let errs = process_binds rest in
                    (shadow @ errs_e @ errs)
                | _ ->
                    let errs = process_binds rest in
                    LetRecNonFunction(x, pos)::errs in
        let errs = process_binds binds in
        errs @ wf_E body new_env
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env  @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env  @ wf_E t env  @ wf_E f env
    | ETuple(expr_ls, _) -> List.flatten (List.map (fun e -> wf_E e env ) expr_ls)
    | EGetItem(tup, idx, _) -> wf_E tup env   @ wf_E idx env
    | ENumber(n, pos) ->
        if n > 1073741823 || n < -1073741824 then [Overflow(n, pos)] else []
    | EBool _ -> []
    | EId(x, pos) ->
        (try ignore (List.assoc x env); [] with Not_found -> [UnboundId(x, pos)])
    | EApp(func, args_ls, pos) ->
        (wf_E func env) @ (List.flatten (List.map (fun x -> wf_E x env) args_ls))
    | ELambda(args, body, pos) ->
        let rec dupe x args =
            match args with
            | [] -> None
            | (y, pos)::_ when x = y -> Some pos
            | _::rest -> dupe x rest in
        let rec process_args args =
            match args with
            | [] -> []
            | (x, pos)::rest -> (match dupe x rest with
                | None -> []
                | Some where -> [DuplicateId(x, where, pos)]) @ process_args rest in
        (process_args args) @ (wf_E body (args @ env))
in wf_E p []

let anf (p : tag program) : unit aprogram =
let rec helpC (e : tag expr) : (unit cexpr * (string * unit cexpr * bool) list) =
    match e with
    | ELet([], body, _) -> helpC body
    | ELet((name, expr, _)::rest, body, pos) ->
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans, false)] @ body_setup)
    | ELetRec([], body, _) -> helpC body
    | ELetRec((name, expr, _)::rest, body, pos) ->
        (* TODO: This is no different from ELet *)
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpC (ELetRec(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans, true)] @ body_setup)
    | EPrim1(op, arg, _) ->
        let (arg_imm, arg_setup) = helpI arg in
        (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
        let (left_imm, left_setup) = helpI left in
        let (right_imm, right_setup) = helpI right in
        (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
        let (cond_imm, cond_setup) = helpI cond in
        (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ETuple(expr_ls, _) ->
        let (ans, setup) = help_foldI expr_ls in
        (CTuple(ans, ()), setup)
    | EGetItem(tup, idx, _) ->
        let (tup_ans, tup_setup) = helpI tup in
        let (idx_ans, idx_setup) = helpI idx in
        (CGetItem(tup_ans, idx_ans, ()), tup_setup @ idx_setup)
    | EApp(func, args_ls, _) ->
        let (ans_func, setup_func) = helpI func in
        let (ans_args, setup_args) = help_foldI args_ls in
        (CApp(ans_func, ans_args, ()), setup_func @ setup_args)
    | ELambda(args, body, _) ->
        (CLambda(List.map fst args, helpA body, ()), [])
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)
and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr * bool) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(id, _) -> (ImmId(id, ()), [])
    | EPrim1(op, arg, tag) ->
        let name = sprintf "unary_%d" tag in
        let (arg_imm, arg_setup) = helpI arg in
        (ImmId(name, ()), arg_setup @ [(name, CPrim1(op, arg_imm, ()), false)])
    | EPrim2(op, left, right, tag) ->
        let name = sprintf "binop_%d" tag in
        let (left_imm, left_setup) = helpI left in
        let (right_imm, right_setup) = helpI right in
        (ImmId(name, ()), left_setup @ right_setup @ [(name, CPrim2(op, left_imm, right_imm, ()), false)])
    | EIf(cond, _then, _else, tag) ->
        let name = sprintf "if_%d" tag in
        let (cond_imm, cond_setup) = helpI cond in
        (ImmId(name, ()), cond_setup @ [(name, CIf(cond_imm, helpA _then, helpA _else, ()), false)])
    | EApp(func, args_ls, tag) ->
        let name = sprintf "func_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans, false)])
    | ETuple(expr_ls, tag) ->
        let name = sprintf "tuple_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans, false)])
    | EGetItem(tup, idx, tag) ->
        let name = sprintf "getitem_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans, false)])
    | ELet([], body, _) -> helpI body
    | ELet((name, expr, _)::rest, body, pos) ->
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans, false)] @ body_setup)
    | ELetRec([], body, _) -> helpI body
    | ELetRec((name, expr, _)::rest, body, pos) ->
        (* TODO: This is no different from ELet *)
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpI (ELetRec(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans, true)] @ body_setup)
    | ELambda(args, body, tag) ->
        let name = sprintf "lambda_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans, false)])
and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    List.fold_right
        (fun (bind, exp, is_rec) body ->
            if is_rec then ALetRec(bind, exp, body, ())
            else ALet(bind, exp, body, ()))
        ans_setup
        (ACExpr ans)
and help_foldI expr_ls = List.fold_left
    (fun (prev_ans, prev_setup) expr ->
        let (ans, setup) = helpI expr in
        (ans::prev_ans, setup @ prev_setup))
    ([], [])
    expr_ls
in helpA p

(* TODO: LetRec recursion *)

(*let anf (p : tag program) : unit aprogram =*)
(*let rec helpC (e : tag expr) r : (unit cexpr * (string * unit cexpr) list) =*)
    (*match e with*)
    (*| ELet([], body, _) -> helpC body false*)
    (*| ELet((name, expr, _)::rest, body, pos) ->*)
        (*let (expr_ans, expr_setup) = helpC expr false in*)
        (*let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) false in*)
        (*(body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)*)
    (*| ELetRec([], body, _) -> helpC body false*)
    (*| ELetRec((name, expr, _)::rest, body, pos) ->*)
        (*(* TODO: This is no different from ELet *)*)
        (*let (expr_ans, expr_setup) = helpC expr true in*)
        (*let (body_ans, body_setup) = helpC (ELetRec(rest, body, pos)) true in*)
        (*(body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)*)
    (*| EPrim1(op, arg, _) ->*)
        (*let (arg_imm, arg_setup) = helpI arg r in*)
        (*(CPrim1(op, arg_imm, ()), arg_setup)*)
    (*| EPrim2(op, left, right, _) ->*)
        (*let (left_imm, left_setup) = helpI left r in*)
        (*let (right_imm, right_setup) = helpI right r in*)
        (*(CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)*)
    (*| EIf(cond, _then, _else, _) ->*)
        (*let (cond_imm, cond_setup) = helpI cond r in*)
        (*(CIf(cond_imm, helpA _then r, helpA _else r, ()), cond_setup)*)
    (*| ETuple(expr_ls, _) ->*)
        (*let (ans, setup) = help_foldI expr_ls r in*)
        (*(CTuple(ans, ()), setup)*)
    (*| EGetItem(tup, idx, _) ->*)
        (*let (tup_ans, tup_setup) = helpI tup r in*)
        (*let (idx_ans, idx_setup) = helpI idx r in*)
        (*(CGetItem(tup_ans, idx_ans, ()), tup_setup @ idx_setup)*)
    (*| EApp(func, args_ls, _) ->*)
        (*let (ans_func, setup_func) = helpI func r in*)
        (*let (ans_args, setup_args) = help_foldI args_ls r in*)
        (*(CApp(ans_func, ans_args, ()), setup_func @ setup_args)*)
    (*| ELambda(args, body, _) ->*)
        (*(CLambda(List.map fst args, helpA body r, ()), [])*)
    (*| _ -> let (imm, setup) = helpI e r in (CImmExpr imm, setup)*)
(*and helpI (e : tag expr) r : (unit immexpr * (string * unit cexpr) list) =*)
    (*match e with*)
    (*| ENumber(n, _) -> (ImmNum(n, ()), [])*)
    (*| EBool(b, _) -> (ImmBool(b, ()), [])*)
    (*| EId(id, _) -> (ImmId(id, ()), [])*)
    (*| EPrim1(op, arg, tag) ->*)
        (*let name = sprintf "unary_%d" tag in*)
        (*let (arg_imm, arg_setup) = helpI arg r in*)
        (*(ImmId(name, ()), arg_setup @ [(name, CPrim1(op, arg_imm, ()))])*)
    (*| EPrim2(op, left, right, tag) ->*)
        (*let name = sprintf "binop_%d" tag in*)
        (*let (left_imm, left_setup) = helpI left r in*)
        (*let (right_imm, right_setup) = helpI right r in*)
        (*(ImmId(name, ()), left_setup @ right_setup @ [(name, CPrim2(op, left_imm, right_imm, ()))])*)
    (*| EIf(cond, _then, _else, tag) ->*)
        (*let name = sprintf "if_%d" tag in*)
        (*let (cond_imm, cond_setup) = helpI cond r in*)
        (*(ImmId(name, ()), cond_setup @ [(name, CIf(cond_imm, helpA _then r, helpA _else r, ()))])*)
    (*| EApp(func, args_ls, tag) ->*)
        (*let name = sprintf "func_%d" tag in*)
        (*let (ans, setup) = helpC e r in*)
        (*(ImmId(name, ()), setup @ [(name, ans)])*)
    (*| ETuple(expr_ls, tag) ->*)
        (*let name = sprintf "tuple_%d" tag in*)
        (*let (ans, setup) = helpC e r in*)
        (*(ImmId(name, ()), setup @ [(name, ans)])*)
    (*| EGetItem(tup, idx, tag) ->*)
        (*let name = sprintf "getitem_%d" tag in*)
        (*let (ans, setup) = helpC e r in*)
        (*(ImmId(name, ()), setup @ [(name, ans)])*)
    (*| ELet([], body, _) -> helpI body false*)
    (*| ELet((name, expr, _)::rest, body, pos) ->*)
        (*let (expr_ans, expr_setup) = helpC expr false in*)
        (*let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) false in*)
        (*(body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)*)
    (*| ELetRec([], body, _) -> helpI body false*)
    (*| ELetRec((name, expr, _)::rest, body, pos) ->*)
        (*(* TODO: This is no different from ELet *)*)
        (*let (expr_ans, expr_setup) = helpC expr true in*)
        (*let (body_ans, body_setup) = helpI (ELetRec(rest, body, pos)) true in*)
        (*(body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)*)
    (*| ELambda(args, body, tag) ->*)
        (*let name = sprintf "lambda_%d" tag in*)
        (*let (ans, setup) = helpC e r in*)
        (*(ImmId(name, ()), setup @ [(name, ans)])*)
(*and helpA e r : unit aexpr =*)
    (*let (ans, ans_setup) = helpC e r in*)
    (*let func =*)
        (*if r then*)
            (*(fun (bind, exp) body -> ALet(bind, exp, body, ()))*)
        (*else*)
            (*(fun (bind, exp) body -> ALetRec(bind, exp, body, ())) in*)
    (*List.fold_right func ans_setup (ACExpr ans)*)
(*and help_foldI expr_ls r = List.fold_left*)
    (*(fun (prev_ans, prev_setup) expr ->*)
        (*let (ans, setup) = helpI expr r in*)
        (*(ans::prev_ans, setup @ prev_setup))*)
    (*([], [])*)
    (*expr_ls*)
(*in match p with*)
    (*| ELetRec _ -> helpA p true*)
    (*| _ -> helpA p false*)
(*;;*)

(* Commonly used constants and macros *)
let const_true_value   = 0xFFFFFFFF
let const_true         = Sized(DWORD_PTR, HexConst(const_true_value))
let const_false_value  = 0x7FFFFFFF
let const_false        = Sized(DWORD_PTR, HexConst(const_false_value))
let bool_mask          = Sized(DWORD_PTR, HexConst(0x80000000))
let tag_as_bool        = Sized(DWORD_PTR, HexConst(0x00000007))
let tag_1_bit          = Sized(DWORD_PTR, HexConst(0x00000001))
let tag_3_bit          = Sized(DWORD_PTR, HexConst(0x00000007))
let tag_func           = Sized(DWORD_PTR, HexConst(0x00000005))
let offset_func        = 0x5

let err_COMP_NOT_NUM   = (Const(01), "__err_COMP_NOT_NUM__")
let err_ARITH_NOT_NUM  = (Const(02), "__err_ARITH_NOT_NUM__")
let err_LOGIC_NOT_BOOL = (Const(03), "__err_LOGIC_NOT_BOOL__")
let err_IF_NOT_BOOL    = (Const(04), "__err_IF_NOT_BOOL__")
let err_OVERFLOW       = (Const(05), "__err_OVERFLOW__")
let err_NOT_TUPLE      = (Const(06), "__err_NOT_TUPLE__")
let err_INDEX_NOT_NUM  = (Const(07), "__err_INDEX_NOT_NUM__")
let err_INDEX_LARGE    = (Const(08), "__err_INDEX_LARGE__")
let err_INDEX_SMALL    = (Const(09), "__err_INDEX_SMALL__")
let err_NOT_LAMBDA     = (Const(10), "__err_NOT_LAMBDA__")
let err_WRONG_ARITY    = (Const(11), "__err_WRONG_ARITY__")

let label_func_begin name = sprintf "%s_func_begin__" name

let rec arg_to_const arg =
    match arg with
    | Const(x) | HexConst(x) -> Some(x)
    | Sized(_, a) -> arg_to_const a
    | _ -> None

let rec arg_to_const arg =
    match arg with
    | Const(x) | HexConst(x) -> Some(x)
    | Sized(_, a) -> arg_to_const a
    | _ -> None

let check_bool arg label =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IMov(Reg(EAX), arg); ]
        else
            [ IJmp(label); ]
    | _ ->
        [ IMov(Reg(EAX), arg);
          ITest(Reg(EAX), tag_as_bool);
          IJz(label); ]

let check_num arg label =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IJmp(label); ]
        else
            [ IMov(Reg(EAX), arg); ]
    | _ ->
        [ IMov(Reg(EAX), arg);
          ITest(Reg(EAX), tag_1_bit);
          IJnz(label); ]

let check_logic arg = check_bool arg (snd err_LOGIC_NOT_BOOL)
let check_if arg = check_bool arg (snd err_IF_NOT_BOOL)
let check_arith arg = check_num arg (snd err_ARITH_NOT_NUM)
let check_index arg = check_num arg (snd err_INDEX_NOT_NUM)
let check_compare arg = check_num arg (snd err_COMP_NOT_NUM)

let block_true_false label op = [
    IMov(Reg(EAX), const_true);
    op label;
    IMov(Reg(EAX), const_false);
    ILabel(label);
]

let rec print_str ls =
    match ls with
    | [] -> ()
    | x::rs -> printf "%s | " x; print_str rs

let rec rm_dup ls =
    let rec rm_from ls x =
        (match ls with
        | [] -> []
        | n::rs when n = x -> rm_from rs x
        | _ -> List.hd ls :: rm_from (List.tl ls) x ) in
    match ls with
    | [] -> []
    | x::rs ->
        let new_ls = rm_from rs x in
        x::rm_dup new_ls

let rec free_a ae env =
    match ae with
    | ALet(name, expr, body, _) ->
        free_c expr env @ free_a body (name::env)
    | ALetRec(name, expr, body, _) ->
        free_c expr env @ free_a body (name::env)
    | ACExpr(e) ->
        free_c e env
and free_c ce env =
    match ce with
    | CIf(con, thn, els, _) ->
        free_i con env @
        free_a thn env @
        free_a els env
    | CPrim1(_, e, _) ->
        free_i e env
    | CPrim2(_, e1, e2, _) ->
        free_i e1 env @
        free_i e2 env
    | CApp(func, args, _) ->
        free_i func env @
        List.flatten (List.map (fun x -> free_i x env) args)
    | CTuple(args, _) ->
        List.flatten (List.map (fun x -> free_i x env) args)
    | CGetItem(tup, idx, _) ->
        free_i tup env @ free_i idx env
    | CLambda(args, expr, _) ->
        free_a expr args
    | CImmExpr(i) ->
        free_i i env
and free_i ie env =
    match ie with
    | ImmNum _ | ImmBool _ -> []
    | ImmId(x, _) ->
        (try ignore (List.find (fun s -> s = x) env); [] with Not_found -> [x])

let free_vars ae = rm_dup (free_a ae [])

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ALetRec(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e + List.length (free_vars e)

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

let rec compile_fun fun_name env e offset =
    let compiled = (compile_aexpr e (offset + 1) env (List.length env - offset) true) in
    let count_local_vars = count_vars e in
    let optimized = optimize compiled in
    (([
        ILabel(fun_name);
        ILineComment("Function prologue");
        IPush(Reg(EBP));
        IMov(Reg(EBP), Reg(ESP)) ]
        @ replicate (IPush(Sized(DWORD_PTR, Const(0)))) count_local_vars),
        ( [ ILabel(label_func_begin fun_name);
            ILineComment("Function body") ]
        @ optimized), [
        ILineComment("Function epilogue");
        IMov(Reg(ESP), Reg(EBP));
        IPop(Reg(EBP));
        IInstrComment(IRet, sprintf "End of %s" fun_name)
    ])
and compile_aexpr e si env num_args is_tail =
    match e with
    (* TODO: This is no different from ELet *)
    | ALetRec(name, lambda, body, _) ->
        let rec rec_env e si env =
            match e with
            | ALetRec(name, _, body, _) ->
                (try ignore (List.assoc name env);
                    rec_env body si env
                with Not_found ->
                    let (new_env, new_si) = rec_env body (si+1) env in
                    ((name, RegOffset(word_size*(~-si), EBP))::new_env, new_si))
            | _ -> ([], si) in
        let (new_env, new_si) = rec_env e si env in
        (*print_env new_env "rec";*)
        let preload = [
            ILineComment(sprintf "Preload function %s" name);
            IMov(Reg(EDX), Reg(ESI));
            IOr(Reg(EDX), tag_func);
            IMov(find new_env name, Reg(EDX));
        ] in
        let func = compile_cexpr lambda new_si (new_env @ env) num_args false in
        let main = compile_aexpr body new_si (new_env @ env) num_args true in
        let cmt = comment lambda name in
        cmt @ preload @ func @ main
    | ALet(name, expr, body, _) ->
        let arg = RegOffset(~-si*word_size, EBP) in
        let new_env = (name, arg)::env in
        let setup = compile_cexpr expr si env num_args false in
        let main = compile_aexpr body (si+1) new_env num_args true in
        let cmt = comment expr name in
        cmt @ setup @ [ IMov(arg, Reg(EAX)) ] @ main
    | ACExpr(e) ->
        compile_cexpr e si env num_args true
and compile_cexpr e si env num_args is_tail =
    match e with
    | CIf (cnd, thn, els, t) ->
        let label_false = sprintf "__if_%d_false__" t in
        let label = sprintf "__if_%d_done__" t in
        let argCond = compile_imm cnd env in
        check_if argCond @ [
            ICmp(Reg(EAX), const_false);
            IJe(label_false);
        ] @ compile_aexpr thn si env num_args true @ [
            IJmp(label);
            ILabel(label_false);
        ] @ compile_aexpr els si env num_args true @ [
            ILabel(label);
        ]
    | CPrim1(op, e, t) ->
        let arg = compile_imm e env in
        let label = sprintf "__isboolnum_done_%d__" t in
        (match op with
        | Add1 ->
            check_arith arg @ [
            IAdd(Reg(EAX), Const(1 lsl 1));
            IJo(snd err_OVERFLOW);
        ]
        | Sub1 ->
            check_arith arg @ [
            ISub(Reg(EAX), Const(1 lsl 1));
            IJo(snd err_OVERFLOW);
        ]
        | IsBool ->
            [ IMov(Reg(EAX), arg); ITest(Reg(EAX), tag_as_bool); ] @
            block_true_false label (fun x -> IJnz(x))
        | IsNum ->
            [ IMov(Reg(EAX), arg); ITest(Reg(EAX), tag_as_bool); ] @
            block_true_false label (fun x -> IJnz(x))
        | Not ->
            check_logic arg @ [
            IXor(Reg(EAX), bool_mask);
        ]
        | PrintStack ->
            failwith "PrintStack not implemented"
        | Print -> [
            IMov(Reg(EAX), arg);
            IPush(Reg(EAX));
            ICall("print");
            IPop(Reg(EAX));
        ]
        | IsTuple ->
            [ IMov(Reg(EAX), arg); IAnd(Reg(EAX), tag_as_bool); ICmp(Reg(EAX), HexConst(0x1)); ] @
            block_true_false label (fun x -> IJne(x))
        )
    | CPrim2(op, e1, e2, t) ->
        let arg1 = compile_imm e1 env in
        let arg2 = compile_imm e2 env in
        let label = sprintf "__compare_%d__" t in
        let comp op = [ ICmp(Reg(EAX), arg2); ] @ block_true_false label op in
        let prelude = match op with
            | Plus | Minus | Times -> check_arith arg2 @ check_arith arg1
            | Greater | GreaterEq | Less | LessEq -> check_compare arg2 @ check_compare arg1
            | And | Or -> check_logic arg2 @ check_logic arg1
            | _ -> []
        in prelude @ (match op with
        | Plus -> [
            IAdd(Reg(EAX), arg2);
            IJo(snd err_OVERFLOW);
        ]
        | Minus -> [
            ISub(Reg(EAX), arg2);
            IJo(snd err_OVERFLOW);
        ]
        | Times -> [
            IMul(Reg(EAX), arg2);
            IJo(snd err_OVERFLOW);
            ISar(Reg(EAX), Const(1));
        ]
        | And ->
            [ IAnd(Reg(EAX), arg2); ]
        | Or ->
            [ IOr(Reg(EAX), arg2); ]
        | Greater ->
            comp (fun x -> IJg(x))
        | GreaterEq ->
            comp (fun x -> IJge(x))
        | Less ->
            comp (fun x -> IJl(x))
        | LessEq ->
            comp (fun x -> IJle(x))
        | Eq -> [
            IMov(Reg(EAX), arg1);
            ICmp(Reg(EAX), arg2);
            IMov(Reg(EAX), const_true);
            IJe(label);
            IPush(Sized(DWORD_PTR, arg1));
            IPush(Sized(DWORD_PTR, arg2));
            ICall("equal");
            IAdd(Reg(ESP), Const(word_size * 2));
            ILabel(label);
        ]
        )
    | CLambda(args, expr, t) ->
        let free_ls = rm_dup (free_a expr args) in
        let func_name = sprintf "__lambda_%d__" t in
        let label = sprintf "__lambda_%d_done__" t in
        let mov_free_vars = [ ILineComment("Load free variables to heap"); ] @
            List.flatten ( List.mapi
            (fun i id -> [
                IMov(Reg(EDX), compile_imm (ImmId(id, 0)) env);
                IMov(RegOffset((i+2)*word_size, ESI), Reg(EDX)); ])
            free_ls ) in
        let heap_size =
            let size = List.length free_ls + 2 in
            if size mod 2 = 0 then size
            else size + 1 in
        let setup = [
            IMov(Sized(DWORD_PTR, RegOffset(0, ESI)), Const(List.length args));
            IMov(Sized(DWORD_PTR, RegOffset(word_size, ESI)), Label(func_name));
        ] @ mov_free_vars @ [
            IMov(Reg(EAX), Reg(ESI));
            IOr(Reg(EAX), tag_func);
            IAdd(Reg(ESI), Const(word_size * heap_size));
            IJmp(label);
        ] in
        let func_env =
            List.mapi (fun i id -> (id, RegOffset(word_size*(i+2), EBP))) args @
            List.mapi (fun i id -> (id, RegOffset(word_size*(~-(i+1)), EBP))) free_ls in
        let (prologue, body, epilogue) = compile_fun func_name func_env expr (List.length free_ls) in
        let reload = [
            ILineComment("Reload free variables from heap");
            IMov(Reg(ECX), RegOffset(word_size*(List.length args+2), EBP));
        ] @ List.flatten (List.mapi
            (fun i id -> [
                IMov(Reg(EDX), RegOffset(word_size*(i+2)-offset_func, ECX));
                IMov(RegOffset(word_size*(~-(i+1)), EBP), Reg(EDX));
            ])
            free_ls ) in
        let main = prologue @ reload @ body @ epilogue in
        let post = [ ILabel(label); ] in
        setup @ main @ post
        (* TODO: Implement free variables support *)
        (*failwith "Implement pls"*)
    | CApp(func, args, _) ->
        let tests = [
            IMov(Reg(EAX), compile_imm func env);
            IAnd(Reg(EAX), tag_3_bit);
            ICmp(Reg(EAX), tag_func);
            IJne(snd err_NOT_LAMBDA);
            IMov(Reg(EAX), compile_imm func env);
            IMov(Reg(EBX), RegOffset(~-offset_func, EAX));
            ICmp(Reg(EBX), Const(List.length args));
            IJne(snd err_WRONG_ARITY);
        ] in
        (*if is_tail && (num_args = List.length args) then*)
            (*let setup = List.flatten (List.mapi*)
              (*(fun i a -> [ IMov(Reg(EAX), a); IMov(RegOffset(word_size*(i+2), EBP), Reg(EAX)); ])*)
              (*(List.rev_map (fun a -> compile_imm a env) args)) in*)
            (*let call = [  IInstrComment(IJmp(label_func_begin (id_name func)), "Tail-call") ] in*)
            (*isfunc @ arity @ setup @ call*)
        (*else*)
        (*let setup = [ IPush(Sized(DWORD_PTR, RegOffset(0, EAX)));] @*)
        let setup = [ IPush(Reg(EAX)); ] @
            List.map
            (fun arg -> IPush(Sized(DWORD_PTR, arg)))
            (List.map (fun x -> compile_imm x env) args) in
        let call = [
            IMov(Reg(EAX), RegOffset(word_size-offset_func, EAX));
            ICall("EAX");
        ] in
        let teardown =
            let len = (List.length args + 1) in
            [ IInstrComment(IAdd(Reg(ESP), Const(word_size * len)), sprintf "Pop %d arguments" len) ] in
        let cmt = comment e "" in
        cmt @ tests @ setup @ call @ teardown
    | CImmExpr(e) ->
        [ IMov(Reg(EAX), compile_imm e env) ]
    | CTuple(expr_ls, _) ->
        let size = List.length expr_ls in
        let prelude = [
            IMov(Reg(EAX), Reg(ESI));
            IOr(Reg(EAX), tag_1_bit);
            IMov(Sized(DWORD_PTR, RegOffset(0, ESI)), Const(size)); ] in
        let (_, load) = List.fold_right
            (fun arg (offset, ls) -> (offset+word_size, ls @ [
                IMov(Sized(DWORD_PTR, Reg(EDX)), compile_imm arg env);
                IMov(Sized(DWORD_PTR, RegOffset(offset, ESI)), Reg(EDX));
            ]) )
            expr_ls
            (word_size, []) in
        let padding =
            if size mod 2 = 0 then [ IAdd(Reg(ESI), Const(word_size*(size+2))); ]
            else [ IAdd(Reg(ESI), Const(word_size*(size+1))); ] in
        prelude @ load @ padding
    | CGetItem(tup, idx, _) -> [
        IMov(Reg(ECX), compile_imm tup env);
        (* TODO: Better testing *)
        ITest(Reg(ECX), tag_1_bit);
        IJz(snd err_NOT_TUPLE);
        ISub(Reg(ECX), Const(1)); ]
      @ check_index (compile_imm idx env) @ [
        ISar(Reg(EAX), Const(1));
        ICmp(Reg(EAX), Const(0));
        IJl(snd err_INDEX_SMALL);
        IAdd(Reg(EAX), Const(1));
        IMov(Reg(EDX), RegOffset(0, ECX));
        ICmp(Reg(EAX), Reg(EDX));
        IJg(snd err_INDEX_LARGE);
        IMov(Reg(EAX), RegOffsetReg(ECX, EAX, word_size, 0));
        ]
and compile_imm e env =
    match e with
    | ImmNum(n, _) -> Const(n lsl 1)
    | ImmBool(true, _) -> const_true
    | ImmBool(false, _) -> const_false
    | ImmId(x, _) -> (find env x)
and id_name e =
    match e with
    | ImmId(x, _) -> x
    | _ -> failwith "Not a variable!"
and comment e s =
    match e with
    | CLambda _ -> [ ILineComment(sprintf "Function/Lambda: %s" s); ]
    | CApp(func, _, _) -> [ ILineComment(sprintf "Function/Lambda call: %s" (id_name func)) ;]
    | _ -> []
and optimize ls =
    match ls with
    | [] -> []
    | IMov(RegOffset(o1, b1), Reg(r1))::IMov(Reg(r2), RegOffset(o2, b2))::rest ->
        if o1 = o2 && b1 = b2 && r1 = r2 then
            (List.hd ls)::optimize rest
        else
            (List.hd ls)::optimize (List.tl ls)
    | what::rest ->
        what::optimize rest
;;

let compile_prog anfed =
  let prelude =
    "section .text
extern error
extern print
extern input
extern equal
extern print_stack
global our_code_starts_here" in
    let suffix =
        let call err = [ ILabel(snd err); IPush(fst err); ICall("error"); ] in
        to_asm (List.flatten [
            call err_COMP_NOT_NUM;
            call err_ARITH_NOT_NUM;
            call err_LOGIC_NOT_BOOL;
            call err_IF_NOT_BOOL;
            call err_OVERFLOW;
            call err_NOT_TUPLE;
            call err_INDEX_NOT_NUM;
            call err_INDEX_LARGE;
            call err_INDEX_SMALL;
            call err_NOT_LAMBDA;
            call err_WRONG_ARITY;
        ]) in
    let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" [] anfed 0 in
    let heap_start = [
        ILineComment("heap start");
        IInstrComment(IMov(Reg(ESI), RegOffset(8, EBP)), "Load ESI with our argument, the heap pointer");
        IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");
        IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
    ] in
    let main = (prologue @ heap_start @ comp_main @ epilogue) in
    sprintf "%s\n%s\n%s\n" prelude (to_asm main) suffix

let compile_to_string prog : (exn list, string) either =
    (*let ext_funcs = [DExt("print", 1); DExt("input", 0)] in*)
    (*let errors = well_formed (Program(ext_funcs @ decls, body, t)) in*)
    let errors = well_formed prog in
    match errors with
    | [] ->
       let tagged : tag program = tag prog in
       let anfed : tag aprogram = atag (anf tagged) in
       (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
       (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
       (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
       Right(compile_prog anfed)
    | _ -> Left(errors)
