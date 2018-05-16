open GT       
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show

(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| instruction :: rest_program ->
   match instruction with
      | BINOP op ->
        let y::x::tl_stack = stack
        in eval env (cstack, (Value.of_int @@ Expr.to_func op (Value.to_int x) (Value.to_int y)) :: tl_stack, c) rest_program
      | CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) rest_program
      | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) rest_program
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) rest_program
      | ST x     -> let z::tl_stack    = stack in eval env (cstack, tl_stack, (State.update x z st, i, o)) rest_program
      | STA (x, n) ->
        let z::rest, stk = split (n + 1) stack in eval env (cstack, stk, (Language.Stmt.update st x z (List.rev rest), i, o)) rest_program
      | LABEL _ -> eval env conf rest_program
      | JMP label -> eval env conf (env#labeled label)
      | CJMP (condition, label) ->
        let v :: tl_stack = stack in
        let x = Value.to_int v in
        eval env (cstack, tl_stack, c) (if (condition = "nz" && x != 0 || condition = "z" && x = 0)
                                        then (env#labeled label) else rest_program)
      | SEXP (t, n) -> let vars, rest_stack = split n stack in
        eval env (cstack, (Value.sexp t (List.rev vars)) :: rest_stack, c) rest_program
      | CALL (f_name, n, p) ->
        if env#is_label f_name then
          eval env ((rest_program, st)::cstack, stack, c) (env#labeled f_name)
        else
          eval env (env#builtin conf f_name n p) rest_program
      | BEGIN (_, args, local_vars) ->
        let current_state = State.enter st (args @ local_vars) in
        let (res_state, res_stack) = List.fold_right (fun arg (st, v::tl_stack) -> (State.update arg v st, tl_stack)) args (current_state, stack) in
        eval env (cstack, res_stack, (res_state, i, o)) rest_program
      | END | RET _ ->
        (match cstack with
        | [] -> conf
        | (stmts, s) :: tl_cstack -> eval env (tl_cstack, stack, (State.leave st s, i, o)) stmts)
      | DROP -> eval env (cstack, List.tl stack, c) rest_program
      | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) rest_program
      | DUP -> let h :: _ = stack in eval env (cstack, h :: stack, c) rest_program
      | SWAP -> let x :: y :: rest_stack = stack in eval env (cstack, y :: x :: rest_stack, c) rest_program
      | ENTER xs -> let vars, stk = split (List.length xs) stack in
       eval env (cstack, stk, (State.push st (List.fold_left2 (fun s x v -> State.bind v x s) State.undefined vars xs) xs, i, o)) rest_program
      | TAG s ->
        let h::rest_stack = stack in
        let res = (match h with Value.Sexp (t, _) -> Value.of_int @@ if t = s then 1 else 0 | _ -> Value.of_int 0) in
       eval env (cstack, res::rest_stack, c) rest_program

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) =
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
  and pattern lfalse = function
      |Stmt.Pattern.Wildcard | Stmt.Pattern.Ident _ -> [DROP]
      | Stmt.Pattern.Sexp (t, ps) -> [DUP; TAG t; CJMP ("z", lfalse)] @ (List.concat (List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ pattern lfalse p) ps))
  and bindings p =
    let rec bind = function
      | Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident _ -> [SWAP]
      | Stmt.Pattern.Sexp (t, ps) ->
        (List.flatten (List.mapi (fun i pi -> [DUP; CONST i; CALL (".elem",  2, false)] @ bind pi) ps)) @ [DROP]
    in bind p @ [ENTER (Stmt.Pattern.vars p)]
  and expr e =
    (match e with
    | Expr.Const c -> [CONST c]
    | Expr.Var v -> [LD v]
    | Expr.String s -> [STRING s]
    | Expr.Array a -> call ".array" a false
    | Expr.Binop (op, expr1, expr2) -> (expr expr1) @ (expr expr2) @ [BINOP op]
    | Expr.Call (f_name, args) -> call (label f_name) args false
    | Expr.Length e -> call ".length" [e] false
    | Expr.Elem (e, i) -> call ".elem" [e; i] false
    | Expr.Sexp (t, e) -> (List.concat @@ List.map expr e) @ [SEXP (t, List.length e)])
  in
  let rec compile_stmt l env stmt =
  (match stmt with
    | Stmt.Assign (name, [], e) -> env, false, expr e @ [ST name]
    | Stmt.Assign (name, ids, e) -> env, false, (List.flatten (List.map expr (ids @ [e]))) @ [STA (name, List.length ids)]
    | Stmt.Seq (stmt1, stmt2) ->
        let env, _, compiled1 = compile_stmt l env stmt1 in
        let env, _, compiled2 = compile_stmt l env stmt2 in
      env, false, compiled1 @ compiled2
    | Stmt.Skip -> env, false, []
    | Stmt.If (cond, th, els) ->
        let else_start_point, env = env#get_label in
        let endif_point, env = env#get_label in
        let env, _, true_b = compile_stmt l env th in
        let env, _, false_b = compile_stmt l env els in
      env, false, (expr cond) @ [CJMP ("z", else_start_point)] @ true_b @ [JMP endif_point; LABEL else_start_point] @ false_b @ [LABEL endif_point]
    | Stmt.While (cond, body) ->
        let start_point, env = env#get_label in
        let end_point, env = env#get_label in
        let env, _, body = compile_stmt l env body in
      env, false, [LABEL start_point] @ (expr cond) @ [CJMP ("z", end_point)] @ body @ [JMP start_point; LABEL end_point]
    | Stmt.Repeat (body, cond) ->
        let start_point, env = env#get_label in
        let env, _, body = compile_stmt l env body in
      env, false, [LABEL start_point] @ body @ (expr cond) @ [CJMP ("z", start_point)]
    | Stmt.Call (f_name, args) -> env, false, call (label f_name) args true
    | Stmt.Return maybe_val -> env, false, (match maybe_val with Some v -> (expr v) @ [RET true] | _ -> [RET false])
    | Stmt.Leave -> env, false, [LEAVE]
    | Stmt.Case (e, branches) ->
       let rec case_branch env lbl is_first lend = (function
         [] -> env, []
         | (p, body)::rest ->
           let env, _, body = compile_stmt l env body in
           let lf, env = env#get_label
           and start = if is_first then [] else [LABEL lbl] in
           let env, code = case_branch env lf false lend rest in
           env, start @ (pattern lf p) @ bindings p @ body @ [LEAVE; JMP lend] @ code) in
       let label_end, env = env#get_label in
       let res_env, compiled_code = case_branch env "" true label_end branches in
       res_env, false, (expr e) @ compiled_code @ [LABEL label_end])
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)

