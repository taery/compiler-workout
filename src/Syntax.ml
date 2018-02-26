(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (st, input_s, output_s) stmt: config = 
      match stmt with 
        | Read name -> (Expr.update name (List.hd input_s) st, List.tl input_s, output_s)
        | Write expr -> let res = Expr.eval st expr in 
            (st, input_s, output_s @ [res])
        | Assign (name, expr) -> (Expr.update name (Expr.eval st expr) st, input_s, output_s)
        | Seq (stmt1, stmt2) -> eval (eval (st, input_s, output_s) stmt1) stmt2;;                                        
  end
