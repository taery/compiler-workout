open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((stack, ((st, i, o) as c)) as conf)  = function
| [] -> conf
| instruction :: rest_program ->
   match instruction with
      | BINOP op -> let y::x::tl_stack = stack in eval env (Expr.eval st (Expr.Binop (op, Expr.Const x, Expr.Const y)) :: tl_stack, c) rest_program
      | READ     -> let z::i'        = i     in eval env (z::stack, (st, i', o)) rest_program
      | WRITE    -> let z::tl_stack    = stack in eval env (tl_stack, (st, i, o @ [z])) rest_program
      | CONST i  -> eval env (i::stack, c) rest_program
      | LD x     -> eval env (st x :: stack, c) rest_program
      | ST x     -> let z::tl_stack    = stack in eval env (tl_stack, (Expr.update x z st, i, o)) rest_program
      | LABEL _ -> eval env conf rest_program
      | JMP label -> eval env conf (env#labeled label)
      | CJMP (condition, label) ->
        let x :: tl_stack = stack in
        eval env (tl_stack, c) (if (condition = "nz" && x != 0 || condition = "z" && x = 0)
                              then (env#labeled label) else rest_program)

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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

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

let rec compile stmt =
  let rec compile_expr expr =
    match expr with
    | Expr.Const c -> [CONST c]
    | Expr.Var v -> [LD v]
    | Expr.Binop (op, expr1, expr2) -> (compile_expr expr1) @ (compile_expr expr2) @ [BINOP op] in
  match stmt with
  | Stmt.Read name -> [READ;ST name]
  | Stmt.Write expr -> compile_expr expr @ [WRITE]
  | Stmt.Assign (name, expr) -> compile_expr expr @ [ST name]
  | Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2
  | Stmt.Skip -> []
  | Stmt.If (cond, th, els) ->
    let else_start_point = labels#generate in
    let endif_point = labels#generate in
    (compile_expr cond) @ [CJMP ("z", else_start_point)] @ (compile th)@ [JMP endif_point; LABEL else_start_point] @ (compile els) @ [LABEL endif_point]
  | Stmt.While (cond, body) ->
    let start_point = labels#generate in
    let end_point = labels#generate in
      [LABEL start_point] @ (compile_expr cond) @ [CJMP ("z", end_point)] @ (compile body) @ [JMP start_point; LABEL end_point]
  | Stmt.RepeatUntil (body, cond) ->
    let start_point = labels#generate in
      [LABEL start_point] @ (compile body) @ (compile_expr cond) @ [CJMP ("z", start_point)]
