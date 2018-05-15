open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show

(* The type for the stack machine program *)
type prg = insn list

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
        match cstack with
        | [] -> conf
        | (stmts, s) :: tl_cstack -> eval env (tl_cstack, stack, (State.leave st s, i, o)) stmts

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
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

let labels =
  object
    val mutable count = 0
    method generate =
        count <- count + 1;
        "label_" ^ string_of_int count
    end

let rec compile_expr expr =
    match expr with
    | Expr.Const c -> [CONST c]
    | Expr.Var v -> [LD v]
    | Expr.String s -> [STRING s]
    | Expr.Array a -> (List.concat (List.map compile_expr a)) @ [CALL ("$array", List.length a, false)]
    | Expr.Binop (op, expr1, expr2) -> (compile_expr expr1) @ (compile_expr expr2) @ [BINOP op]
    | Expr.Call (f_name, args) -> List.concat (List.map compile_expr (List.rev args)) @ [CALL ("L" ^ f_name, List.length args, false)]
    | Expr.Length e -> (compile_expr e) @ [CALL ("$length", 1, false)]
    | Expr.Elem (e, i) -> (compile_expr e) @ (compile_expr i) @ [CALL ("$elem", 2, false)]

let rec compile_statements stmts =
    match stmts with
    | Stmt.Assign (name, [], expr) -> compile_expr expr @ [ST name]
    | Stmt.Assign (name, ids, expr) -> List.flatten (List.map compile_expr (ids @ [expr])) @ [STA (name, List.length ids)]
    | Stmt.Seq (stmt1, stmt2) -> compile_statements stmt1 @ compile_statements stmt2
    | Stmt.Skip -> []
    | Stmt.If (cond, th, els) ->
      let else_start_point = labels#generate in
      let endif_point = labels#generate in
      (compile_expr cond) @ [CJMP ("z", else_start_point)] @ (compile_statements th)@ [JMP endif_point; LABEL else_start_point] @ (compile_statements els) @ [LABEL endif_point]
    | Stmt.While (cond, body) ->
      let start_point = labels#generate in
      let end_point = labels#generate in
      [LABEL start_point] @ (compile_expr cond) @ [CJMP ("z", end_point)] @ (compile_statements body) @ [JMP start_point; LABEL end_point]
    | Stmt.Repeat (body, cond) ->
      let start_point = labels#generate in
      [LABEL start_point] @ (compile_statements body) @ (compile_expr cond) @ [CJMP ("z", start_point)]
    | Stmt.Call (f_name, args) -> List.concat (List.map compile_expr args) @ [CALL ("L"^f_name, List.length args, true)]
    | Stmt.Return maybe_val -> match maybe_val with Some v -> (compile_expr v) @ [RET true] | _ -> [RET false]

let compile_definition (f_name, (args, local_vars, body)) = [LABEL f_name; BEGIN (f_name, args, local_vars)] @ (compile_statements body) @ [END]

let rec compile (defs, program) =
  (compile_statements program) @ [END] @ (List.concat (List.map compile_definition defs))