open GT   
open Syntax    
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval cfg program: config = 
	let run_instruction (stack, (state, input_s, output_s)) instruction: config = 
	  match instruction with
	   | BINOP op -> (match stack with 
	                  | left :: right :: rest_stk -> 
	                     let bin_expr = Expr.Binop (op, Expr.Const left, Expr.Const right) in 
	                     (Expr.eval state bin_expr :: rest_stk, (state, input_s, output_s))
	                  | _ -> failwith "Not enouth arguments for binary operation")
	   | CONST c -> (c :: stack, (state, input_s, output_s)) 
	   | READ -> (List.hd input_s :: stack, (state, List.tl input_s, output_s))
	   | WRITE -> (List.tl stack, (state, input_s, output_s @ [List.hd stack]))
	   | LD v -> (state v :: stack, (state, input_s, output_s))
	   | ST v -> (List.tl stack, (Expr.update v (List.hd stack) state, input_s, output_s)) in 
	match program with
	| hd_instr :: rest_program -> eval (run_instruction cfg hd_instr) rest_program
	| [] -> cfg

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

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
  | Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2;;                      
