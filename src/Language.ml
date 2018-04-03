(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open List
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let undefined_error scope_name = fun x -> failwith @@ (Printf.sprintf "Undefined %s variable %s" scope_name x) in
      { g = undefined_error "global"; l = undefined_error "local"; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
        let scope_func x scope_name = fun y -> if x = y then v else scope_name y in
        if mem x s.scope then
            {g = s.g; l = scope_func x s.l; scope = s.scope }
        else
            {g = scope_func x s.g; l = s.l; scope = s.scope }

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { g = st.g; l = empty.l; scope = xs }

    (* Drops a scope *)
    let leave st st' = { g = st.g; l = st'.l; scope = st'.scope }

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval st expr : int =
      match expr with
        | Const (c) -> c
        | Var (v) -> State.eval st v
        | Binop (op, left, right) ->
          let e_l = eval st left in
          let e_r = eval st right in
          let to_bool cond = if cond == 0 then false else true in
          let to_int b = if b then 1 else 0 in
            match op with
              | "!!" -> to_int (to_bool e_l || to_bool e_r)
              | "&&" -> to_int (to_bool e_l && to_bool e_r)
              | "==" -> to_int (e_l == e_r)
              | "!=" -> to_int (e_l != e_r)
              | ">=" -> to_int (e_l >= e_r)
              | "<=" -> to_int (e_l <= e_r)
              | ">" -> to_int (e_l > e_r)
              | "<" -> to_int (e_l < e_r)
              | "+" -> e_l + e_r
              | "-" -> e_l - e_r
              | "*" -> e_l * e_r
              | "/" -> e_l / e_r
              | "%" -> e_l mod e_r
              | _ -> failwith (Printf.sprintf "Unknown operation %s" op);;

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)

    let to_binop ops = List.map (fun op -> ostap ($(op)), fun x y -> Binop(op, x, y)) ops

    ostap (
      parse: expr;
      expr:
        !(Util.expr
          (fun x -> x)
          [|
            `Lefta, to_binop ["!!"];
            `Lefta, to_binop ["&&"];
            `Nona, to_binop ["=="; "<="; "<"; ">="; ">"; "!="];
            `Lefta, to_binop ["+"; "-"];
            `Lefta, to_binop ["*"; "/"; "%"];
          |]
          primary
        );
      primary: x:IDENT { Var x } | n:DECIMAL { Const n } | -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, input_s, output_s) as cfg) stmt =
      match stmt with
        | Read name -> (State.update name (hd input_s) st, tl input_s, output_s)
        | Write expr -> (st, input_s, output_s @ [Expr.eval st expr])
        | Assign (name, expr) -> (State.update name (Expr.eval st expr) st, input_s, output_s)
        | Seq (stmt1, stmt2) -> eval env (eval env cfg stmt1) stmt2
        | Skip -> cfg
        | If (cond, th, els) -> if Expr.eval st cond <> 0 then eval env cfg th else eval env cfg els
        | While (cond, body) -> if Expr.eval st cond <> 0 then eval env (eval env cfg body) stmt else cfg
        | RepeatUntil (body, cond) ->
          let ((res_st, _, _) as res_cfg) = eval env cfg body in
          if Expr.eval res_st cond = 0 then eval env res_cfg stmt else res_cfg
        | Call (f_name, arg_vals) ->
          let (args, local_vars, body) = env#get_definition f_name in
          let new_state = State.enter st (args @ local_vars) in
          let loaded_state = fold_left2 (fun loaded arg v -> State.update arg (Expr.eval st v) loaded) new_state args arg_vals in
          let (res_state, res_input, res_output) = eval env (loaded_state, input_s, output_s) body in
          ((State.leave res_state st), res_input, res_output)

    let rec parse_ifs elifs els = match elifs with
        | [] -> els
        | (i_cond, i_body)::rest_ifs -> If (i_cond, i_body, parse_ifs rest_ifs els)

    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      seq: <s::ss> : !(Util.listBy)[ostap (";")][stmt] { fold_left (fun x y -> Seq (x, y)) s ss};
      stmt: read | write | assign | skip | if_ | while_ | until_ | for_ | func_;
      read: "read" -"(" variable:IDENT -")" { Read variable };
      write: "write" -"(" expr: !(Expr.parse) -")" { Write expr };
      assign: variable:IDENT -":=" expr:!(Expr.parse) { Assign (variable, expr) };
      skip: %"skip" { Skip };
      if_: %"if" condition:!(Expr.parse)
           %"then" then_body:parse
           elif_branches: (%"elif" !(Expr.parse) %"then" parse)*
           else_branch: (%"else" parse)?
           %"fi" { If (condition, then_body, parse_ifs elif_branches (match else_branch with None -> Skip | Some b -> b)) };
      while_: %"while" condition:!(Expr.parse) %"do" body:parse %"od" { While (condition, body) };
      until_: %"repeat" body:parse %"until" condition:!(Expr.parse) { RepeatUntil (body, condition) };
      for_: %"for" i:parse -"," condition:!(Expr.parse) -"," inc:parse %"do" body:parse %"od" {Seq(i, While(condition, Seq(body, inc)))};
      func_: f_name:IDENT -"(" args: !(Expr.parse)* -")" { Call (f_name, args) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: %"fun" name:IDENT -"(" args:(IDENT)* -")" local_vars: (%"local" (IDENT)+)? -"{" body: !(Stmt.parse)-"}"
      { (name, (args, (match local_vars with None -> [] | Some vars -> vars), body)) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module DefenitionsMap = Map.Make (String) in
  let definitions = fold_left (fun map (f_name, definition) -> DefenitionsMap.add f_name definition map) DefenitionsMap.empty defs in
  let env = (object method get_definition d = DefenitionsMap.find d definitions end) in
  let _, _, o = Stmt.eval env (State.empty, i, []) body in o
                                   
(* Top-level parser *)
let parse = ostap(!(Definition.parse) * !(Stmt.parse))
