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

let well_formed (p : (Lexing.position * Lexing.position) program) : exn list =
        (* TODO: Free vars and shit *)
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
            let rec process_binds rem_binds env =
                match rem_binds with
                | [] -> (env, [])
                | (x, e, pos)::rest ->
                    match e with
                    | ELambda _ ->
                        let shadow = match dupe x rest with
                            | Some where -> [DuplicateFun(x, where, pos)]
                            | None ->
                                try let existing = List.assoc x env in
                                    [DuplicateFun(x, pos, existing)]
                                with Not_found -> [] in
                        let errs_e = wf_E e env  in
                        let new_env = (x, pos)::env in
                        let (newer_env, errs) = process_binds rest new_env in
                        (newer_env, (shadow @ errs_e @ errs))
                    | _ ->
                        let (new_env, errs) = process_binds rest env in
                        (new_env, LetRecNonFunction(x, pos)::errs) in
            (* TODO: This is no different from ELet *)
            let (env2, errs) = process_binds binds env in
            errs @ wf_E body env2
        | EPrim1(_, e, _) -> wf_E e env
        | EPrim2(_, l, r, _) -> wf_E l env  @ wf_E r env
        | EIf(c, t, f, _) -> wf_E c env  @ wf_E t env  @ wf_E f env
        | ETuple(expr_ls, _) -> List.flatten (List.map (fun e -> wf_E e env ) expr_ls)
        | EGetItem(tup, idx, _) -> wf_E tup env   @ wf_E idx env
        | ENumber(n, pos) ->
            if n > 1073741823 || n < -1073741824 then [Overflow(n, pos)] else []
        | EBool _ -> []
        | EId(x, pos) ->
            (try ignore (List.assoc x env); []
            with Not_found -> [UnboundId(x, pos)])
        | EApp(func, args_ls, pos) ->
            (wf_E func env) @
            (List.flatten (List.map (fun x -> wf_E x env) args_ls))
        | ELambda(args, body, pos) ->
            let rec dupe x args =
                match args with
                | [] -> None
                | (y, pos)::_ when x = y -> Some pos
                | _::rest -> dupe x rest in
            let rec process_args rem_args =
                match rem_args with
                | [] -> []
                | (x, pos)::rest -> (match dupe x rest with
                    | None -> []
                    | Some where -> [DuplicateId(x, where, pos)]) @ process_args rest in
            (process_args args) @ (wf_E body args)
    in wf_E p []

        (* TODO: Free vars and shit *)
let anf (p : tag program) : unit aprogram =
let rec helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) =
    match e with
    | ELet([], body, _) -> helpC body
    | ELet((name, expr, _)::rest, body, pos) ->
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)
    | ELetRec([], body, _) -> helpC body
    | ELetRec((name, expr, _)::rest, body, pos) ->
        (* TODO: This is no different from ELet *)
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpC (ELetRec(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)
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
and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(id, _) -> (ImmId(id, ()), [])
    | EPrim1(op, arg, tag) ->
        let name = sprintf "unary_%d" tag in
        let (arg_imm, arg_setup) = helpI arg in
        (ImmId(name, ()), arg_setup @ [(name, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
        let name = sprintf "binop_%d" tag in
        let (left_imm, left_setup) = helpI left in
        let (right_imm, right_setup) = helpI right in
        (ImmId(name, ()), left_setup @ right_setup @ [(name, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
        let name = sprintf "if_%d" tag in
        let (cond_imm, cond_setup) = helpI cond in
        (ImmId(name, ()), cond_setup @ [(name, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args_ls, tag) ->
        let name = sprintf "func_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans)])
    | ETuple(expr_ls, tag) ->
        let name = sprintf "tuple_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans)])
    | EGetItem(tup, idx, tag) ->
        let name = sprintf "getitem_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans)])
    | ELet([], body, _) -> helpI body
    | ELet((name, expr, _)::rest, body, pos) ->
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)
    | ELetRec([], body, _) -> helpI body
    | ELetRec((name, expr, _)::rest, body, pos) ->
        (* TODO: This is no different from ELet *)
        let (expr_ans, expr_setup) = helpC expr in
        let (body_ans, body_setup) = helpI (ELetRec(rest, body, pos)) in
        (body_ans, expr_setup @ [(name, expr_ans)] @ body_setup)
    | ELambda(args, body, tag) ->
        let name = sprintf "lambda_%d" tag in
        let (ans, setup) = helpC e in
        (ImmId(name, ()), setup @ [(name, ans)])

and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
and help_foldI expr_ls = List.fold_left
    (fun (prev_ans, prev_setup) expr ->
        let (ans, setup) = helpI expr in
        (ans::prev_ans, setup @ prev_setup)
    )
    ([], [])
    expr_ls
in helpA p
;;

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
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

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

let err_COMP_NOT_NUM   = (Const(1), "__err_COMP_NOT_NUM__")
let err_ARITH_NOT_NUM  = (Const(2), "__err_ARITH_NOT_NUM__")
let err_LOGIC_NOT_BOOL = (Const(3), "__err_LOGIC_NOT_BOOL__")
let err_IF_NOT_BOOL    = (Const(4), "__err_IF_NOT_BOOL__")
let err_OVERFLOW       = (Const(5), "__err_OVERFLOW__")
let err_NOT_TUPLE      = (Const(6), "__err_NOT_TUPLE__")
let err_INDEX_NOT_NUM  = (Const(7), "__err_INDEX_NOT_NUM__")
let err_INDEX_LARGE    = (Const(8), "__err_INDEX_LARGE__")
let err_INDEX_SMALL    = (Const(9), "__err_INDEX_SMALL__")

let label_func_begin name = sprintf "__%s_func_begin__" name

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

let rec compile_fun fun_name args e : (instruction list * instruction list * instruction list) =
  let args_env = List.mapi (fun i a -> (a, RegOffset(word_size * (i + 2), EBP))) args in
  let compiled = (compile_aexpr e 1 args_env (List.length args) true) in
  let count_local_vars = count_vars e in
  let optimized = optimize compiled in
  (([
       ILabel(fun_name);
       ILineComment("Function prologue");
       IPush(Reg(EBP));
       IMov(Reg(EBP), Reg(ESP))
     ]
    @ replicate (IPush(Sized(DWORD_PTR, Const(0)))) count_local_vars),
   ([ ILineComment("Function body") ]
    @ [ ILabel(label_func_begin fun_name); ]
    @ optimized),
   [
     ILineComment("Function epilogue");
     IMov(Reg(ESP), Reg(EBP));
     IPop(Reg(EBP));
     IInstrComment(IRet, sprintf "End of %s" fun_name)
  ])
and compile_aexpr e si env num_args is_tail =
    match e with
    (* TODO: This is no different from ELet *)
    | ALetRec(name, exp, body, _) ->
        let setup = compile_cexpr exp si env num_args false in
        let arg = RegOffset(~-si*word_size, EBP) in
        let new_env = (name, arg)::env in
        let main = compile_aexpr body (si+1) new_env num_args true in
        setup @ [ IMov(arg, Reg(EAX)) ] @ main
    | ALet(name, exp, body, _) ->
        let setup = compile_cexpr exp si env num_args false in
        let arg = RegOffset(~-si*word_size, EBP) in
        let new_env = (name, arg)::env in
        let main = compile_aexpr body (si+1) new_env num_args true in
        setup @ [ IMov(arg, Reg(EAX)) ] @ main
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
        (*| Print ->*)
            (*failwith "Printnot implemented"*)
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
(*let rec compile_fun fun_name args e : (instruction list * instruction list * instruction list) =*)
            (*let (compile_fun (sprintf "lambda_%d" t) args body*)
        let (prologue, body, epilogue) = compile_fun (sprintf "lambda_%d" t) args expr in
        (prologue @ body @ epilogue)
        (* No free variables support *)
        (*failwith "Implement pls"*)
    | CApp(func, args, _) ->
        (* Non-tail optimized *)
        call func args env

        (*if is_tail && (num_args = List.length args) then*)
            (*List.flatten (List.mapi*)
              (*(fun i a -> [ IMov(Reg(EAX), a); IMov(RegOffset(word_size*(i+2), EBP), Reg(EAX)); ])*)
              (*(List.rev_map (fun a -> compile_imm a env) args)) @*)
            (*[  IInstrComment(IJmp(label_func_begin name), "Tail-call optimized") ]*)
        (*else*)
           (*call name (List.map (fun a -> compile_imm a env) args)*)
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
and call func args env =
    let isfunc = [
        IMov(Reg(EAX), compile_imm func env);
        IAnd(Reg(EAX), tag_3_bit);
        ICmp(Reg(EAX), tag_func);
        (* TODO: Insert correct error *)
        IJne(snd err_COMP_NOT_NUM);
    ] in let arity = [
        IMov(Reg(EAX), compile_imm func env);
        ISub(Reg(EAX), tag_func);
        IMov(Reg(EBX), RegOffset(0, EAX));
        ICmp(Reg(EBX), Const(List.length args));
        (* TODO: Insert correct error *)
        IJne(snd err_ARITH_NOT_NUM);
    ] in
    let setup = List.map
        (fun arg -> IPush(Sized(DWORD_PTR, arg)))
        (List.map (fun x -> compile_imm x env) args) in
    let call = [
        IMov(Reg(ECX), RegOffset(word_size, EAX));
        ICall("ECX");
    ] in
    let teardown =
        let len = List.length args in
            if len = 0 then []
            else [ IInstrComment(IAdd(Reg(ESP), Const(word_size * len)), sprintf "Pop%d arguments" len) ] in
    [ ILineComment(sprintf "Function %s call" (id_name func)) ;] @
    isfunc @ arity @ setup @ call @ teardown

  (*let setup = List.map (fun arg -> IPush(Sized(DWORD_PTR, arg))) args in*)

(*and call label args =*)
  (*let setup = List.map (fun arg -> IPush(Sized(DWORD_PTR, arg))) args in*)
  (*let teardown =*)
    (*let len = List.length args in*)
    (*if len = 0 then []*)
    (*else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in*)
  (*[ ILineComment(sprintf "Call to function %s" label) ] @ setup @ [ ICall(label) ] @ teardown*)
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
        ]) in
    let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" [] anfed in
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
