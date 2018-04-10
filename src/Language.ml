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
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)

  let to_func op =
    let bti   = function true -> 1 | _ -> 0 in
    let itb b = b <> 0 in
    let (|>) f g   = fun x y -> f (g x y) in
    match op with
    | "+"  -> (+)
    | "-"  -> (-)
    | "*"  -> ( * )
    | "/"  -> (/)
    | "%"  -> (mod)
    | "<"  -> bti |> (< )
    | "<=" -> bti |> (<=)
    | ">"  -> bti |> (> )
    | ">=" -> bti |> (>=)
    | "==" -> bti |> (= )
    | "!=" -> bti |> (<>)
    | "&&" -> fun x y -> bti (itb x && itb y)
    | "!!" -> fun x y -> bti (itb x || itb y)
    | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let rec eval env ((st, i, o, r) as conf) expr =
      match expr with
      | Const n -> (st, i, o, Some n)
      | Var   x -> (st, i, o, Some(State.eval st x))
      | Binop (op, x, y) ->
        let ((_, i, o, Some left) as cfg_left) = eval env conf x in
        let (res_st, res_i, res_o, Some right) = eval env cfg_left y
      in (res_st, res_i, res_o, Some (to_func op left right))
      | Call (f_name, args) ->
        let eval_args (acc, cfg) arg =
            let (_, _, _, Some arg_v) as res_cfg = eval env cfg arg in (arg_v::acc, res_cfg)
        in let arg_vals, res_conf = fold_left eval_args ([], conf) args
      in env#definition env f_name (rev arg_vals) res_conf

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
    *)

    let to_binop ops = map (fun op -> ostap ($(op)), fun x y -> Binop(op, x, y)) ops

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
      primary:
        n:DECIMAL { Const n }
        | f_name:IDENT -"(" args:!(Util.list0)[parse] -")" { Call (f_name, args) }
        |  x:IDENT { Var x }
        | -"(" expr -")"
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let rec eval env ((st, input_s, output_s, ret) as cfg) k stmt =
    let diamond k stmt =
      match k with
      | Skip -> stmt
      | _    -> Seq(stmt, k)
    in
      match stmt with
        | Read name -> eval env (State.update name (hd input_s) st, tl input_s, output_s, ret) Skip k
        | Write expr ->
          let (res_st, res_i, res_o, Some v) = Expr.eval env cfg expr in
         eval env (res_st, res_i, res_o @ [v], ret) Skip k
        | Assign (name, expr) ->
          let (res_st, res_i, res_o, Some v) = Expr.eval env cfg expr in
         eval env (State.update name v res_st, res_i, res_o, ret) Skip k
        | Seq (stmt1, stmt2) -> eval env cfg (diamond k stmt2) stmt1
        | Skip ->
          (match k with
          | Skip -> cfg
          | _    -> eval env cfg Skip k)
        | If (cond, th, els) ->
          let (res_st, res_i, res_o, Some res_cond) = Expr.eval env cfg cond in
          let res_cfg = (res_st, res_i, res_o, ret) in
          if res_cond <> 0 then eval env res_cfg k th else eval env res_cfg k els
        | While (cond, body) ->
          let (res_st, res_i, res_o, Some res_cond) = Expr.eval env cfg cond in
          let res_cfg = (res_st, res_i, res_o, ret) in
          if res_cond <> 0 then eval env res_cfg (diamond k stmt) body else eval env res_cfg Skip k
        | Repeat (body, cond) ->
          let loop =  While (Expr.Binop ("==", cond, Expr.Const 0), body) in
          eval env cfg (diamond k loop) body
        | Return maybe_val -> (match maybe_val with Some v -> Expr.eval env cfg v | _ -> (st, input_s, output_s, None))
        | Call (f_name, args) ->
          eval env (Expr.eval env cfg (Expr.Call (f_name, args))) k Skip

    let rec parse_ifs elifs els = match elifs with
        | [] -> els
        | (i_cond, i_body)::rest_ifs -> If (i_cond, i_body, parse_ifs rest_ifs els)

    ostap (
      parse: seq | stmt;
      seq: <s::ss> : !(Util.listBy)[ostap (";")][stmt] { fold_left (fun x y -> Seq (x, y)) s ss};
      stmt: read | write | assign | skip | if_ | while_ | until_ | for_ | func_ | return_;
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
      until_: %"repeat" body:parse %"until" condition:!(Expr.parse) { Repeat (body, condition) };
      for_: %"for" i:parse -"," condition:!(Expr.parse) -"," inc:parse %"do" body:parse %"od" {Seq(i, While(condition, Seq(body, inc)))};
      return_: %"return" expr: !(Expr.parse)? { Return expr };
      func_: f_name:IDENT -"(" args:!(Expr.parse)* -")" { Call (f_name, args) }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
