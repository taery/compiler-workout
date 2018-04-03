(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval st e : int =
      match e with
        | Const (c) -> c
        | Var (v) -> st v
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
    (* loop with a post-condition       *) | RepeatUntil  of t * Expr.t
    with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((st, input_s, output_s) as cfg) stmt: config =
      match stmt with
        | Read name -> (Expr.update name (List.hd input_s) st, List.tl input_s, output_s)
        | Write expr -> let res = Expr.eval st expr in
            (st, input_s, output_s @ [res])
        | Assign (name, expr) -> (Expr.update name (Expr.eval st expr) st, input_s, output_s)
        | Seq (stmt1, stmt2) -> eval (eval cfg stmt1) stmt2
        | Skip -> cfg
        | If (cond, th, els) -> if Expr.eval st cond <> 0 then eval cfg th else eval cfg els
        | While (cond, body) -> if Expr.eval st cond <> 0 then eval (eval cfg body) stmt else cfg
        | RepeatUntil (body, cond) ->
            let ((res_st, _, _) as res_cfg) = eval cfg body in
            if Expr.eval res_st cond == 0 then eval res_cfg stmt else res_cfg

    let rec parse_ifs elifs els = match elifs with
        | [] -> els
        | (i_cond, i_body)::rest_ifs -> If (i_cond, i_body, parse_ifs rest_ifs els);;

    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      seq: <s::ss> : !(Util.listBy)[ostap (";")][stmt] { List.fold_left (fun x y -> Seq (x, y)) s ss};
      stmt: read | write | assign | skip | if_ | while_ | until_ | for_;
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
      for_: %"for" i:parse -"," condition:!(Expr.parse) -"," inc:parse %"do" body:parse %"od" {Seq(i, While(condition, Seq(body, inc)))}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
