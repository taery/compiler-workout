(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec init_list i n func =
  if i < n then
    (func i) :: (init_list (i+ 1) n func)
  else []

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = init_list 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

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
      | Const n  -> (st, i, o, Some (Value.of_int n))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Var   x  -> (st, i, o, Some (State.eval st x))
      | Elem (e, k) ->
        let (st, i, o, v) = eval_list env conf [e; k] in env#definition env ".elem" v (st, i, o, None)
      | Length e ->
        let (st, i, o, Some v) = eval env conf e in env#definition env ".length" [v] (st, i, o, None)
      | Array a ->
        let (st, i, o, v) = eval_list env conf a in env#definition env ".array" v (st, i, o, None)
      | Sexp (t, xs) ->
        let (st, i, o, v) = eval_list env conf xs in (st, i, o, Some (Value.Sexp (t, v)))
      | Binop (op, x, y) ->
          let ((_, i, o, Some left) as cfg_left) = eval env conf x in
          let (res_st, res_i, res_o, Some right) = eval env cfg_left y
        in (res_st, res_i, res_o, Some (Value.of_int (to_func op (Value.to_int left) (Value.to_int right))))
      | Call (f_name, args) ->
        let eval_args (acc, cfg) arg =
            let (_, _, _, Some arg_v) as res_cfg = eval env cfg arg in (arg_v::acc, res_cfg)
        in let arg_vals, res_conf = List.fold_left eval_args ([], conf) args
      in env#definition env f_name (List.rev arg_vals) res_conf
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)

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
      primary: b:base is:(-"[" e:expr -"]" {`Elem e} | "." %"length" {`Len})* {List.fold_left (fun b -> function `Elem i -> Elem (b, i) | `Len -> Length b) b is};

      base:
        n:DECIMAL { Const n }
        | c: CHAR { Const (Char.code c) }
        | s: STRING { String (String.sub s 1 (String.length s - 2)) }
        | "[" vars:!(Util.list0)[parse] "]" { Array vars }
        | "`" name:IDENT args:(-"(" !(Util.list)[parse] -")")? { Sexp (name, match args with Some v -> v | _ -> [])}
        | f_name:IDENT -"(" args:!(Util.list0)[parse] -")" { Call (f_name, args) }
        |  x:IDENT { Var x }
        | -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)
        ostap (
          parse:
          x:IDENT { Ident x }
          | "_" { Wildcard }
          | "`" name:IDENT body:(-"(" !(Util.list)[parse] -")")? { Sexp (name, match body with Some v -> v | _ -> []) }
        )

        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p

      end

    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
    (* leave a scope                    *) | Leave  with show

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

  let rec eval env ((st, input_s, output_s, ret) as cfg) k stmt =
      let diamond k stmt =
        match k with
        | Skip -> stmt
        | _    -> Seq(stmt, k)
      in
        match stmt with
          | Assign (name, ids, expr) ->
            let (st, i, o, is) = Expr.eval_list env cfg ids in
            let (res_st, res_i, res_o, Some v) = Expr.eval env (st, i, o, None) expr in
           eval env (update res_st name v is, res_i, res_o, None) Skip k
          | Seq (stmt1, stmt2) -> eval env cfg (diamond k stmt2) stmt1
          | Skip ->
            (match k with
            | Skip -> cfg
            | _    -> eval env cfg Skip k)
          | If (cond, th, els) ->
            let (res_st, res_i, res_o, Some res_cond) = Expr.eval env cfg cond in
            let res_cfg = (res_st, res_i, res_o, ret) in
            if (Value.to_int res_cond) <> 0 then eval env res_cfg k th else eval env res_cfg k els
          | While (cond, body) ->
            let (res_st, res_i, res_o, Some res_cond) = Expr.eval env cfg cond in
            let res_cfg = (res_st, res_i, res_o, ret) in
            if (Value.to_int res_cond) <> 0 then eval env res_cfg (diamond k stmt) body else eval env res_cfg Skip k
          | Repeat (body, cond) ->
            let loop =  While (Expr.Binop ("==", cond, Expr.Const 0), body) in
            eval env cfg (diamond k loop) body
          | Return maybe_val -> (match maybe_val with Some v -> Expr.eval env cfg v | _ -> (st, input_s, output_s, None))
          | Call (f_name, args) ->
            eval env (Expr.eval env cfg (Expr.Call (f_name, args))) k Skip
          | Leave -> eval env (State.drop st, input_s, output_s, ret) k Skip
          | Case (expr, branches) ->
            let (_, _, _, Some v) as c = Expr.eval env cfg expr in
            let rec check ((st, i, o, _) as conf) = function
              | [] -> failwith "Pattern is not matched"
              | (p, body)::rest_branches ->
                let rec match_p p v st =
                  let update x v = function
                    | None -> None
                    | Some s -> Some (State.bind x v s)
                  in
                  match p, v with
                    | Pattern.Wildcard, _ -> st
                    | Pattern.Ident x, v -> update x v st
                    | Pattern.Sexp (t1, patterns), Value.Sexp (t2, values) when t1 = t2 -> match_list patterns values st
                    | _ -> None
                and match_list l1 l2 state =
                  match l1, l2 with
                    | [], [] -> state
                    | h1::rest_ps, h2::rest_vs -> match_list rest_ps rest_vs (match_p h1 h2 state)
                    | _ -> None
                in
                  let res = match_p p v (Some State.undefined) in
                  match res with
                   | None -> check conf rest_branches
                   | Some s -> eval env (State.push st s (Pattern.vars p), i, o, None) k (Seq (body, Leave))
             in check c branches


    let rec parse_ifs elifs els = match elifs with
      | [] -> els
      | (i_cond, i_body)::rest_ifs -> If (i_cond, i_body, parse_ifs rest_ifs els)

    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      seq: <s::ss> : !(Util.listBy)[ostap (";")][stmt] { List.fold_left (fun x y -> Seq (x, y)) s ss};
      stmt: assign | skip | if_ | while_ | until_ | for_ | func_ | return_ | case_;
      assign: variable:IDENT ids:(-"[" !(Expr.parse) -"]")* -":=" expr:!(Expr.parse) { Assign (variable, ids, expr) };
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
      func_: f_name:IDENT -"(" args:!(Expr.parse)* -")" { Call (f_name, args) };
      case_: %"case" expr:!(Expr.parse) %"of"
           branches:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)]
             %"esac" { Case (expr, branches) }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
