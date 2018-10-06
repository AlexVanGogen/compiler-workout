(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Matcher
       
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
    let toInt b = if b then 1 else 0
     let toBool n = n <> 0
     
     (* returnInt : (a -> a -> bool) -> (a -> a -> int) *)
     let returnInt op x y = toInt @@ op x y
     
     (* makeInt : (bool -> bool -> bool) -> (int -> int -> int) *)
     let makeInt op x y = toInt @@ op (toBool x) (toBool y)
     
     let rec eval s e =
       match e with
       | Const n -> n
       | Var v -> s v
       | Binop (op, x, y) -> funcOf op (eval s x) (eval s y)
     and funcOf op = 
       match op with
       | "+"  -> ( + )
       | "-"  -> ( - )
       | "*"  -> ( * )
       | "/"  -> ( / )
       | "%"  -> (mod)
       | "<"  -> ( returnInt (<) )
       | "<=" -> ( returnInt (<=) )
       | ">"  -> ( returnInt (>) )
       | ">=" -> ( returnInt (>=) )
       | "==" -> ( returnInt (=) )
       | "!=" -> ( returnInt (<>) )
       | "&&" -> ( makeInt (&&) )
       | "!!" -> ( makeInt (||) )
       | _ -> failwith "Unknown operator"


    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    let make_node op = fun x y -> Binop (op, x, y)

    ostap (
      expr:
        !(Util.expr
        (fun x -> x)
        [|
          `Lefta , [ostap ("!!"), make_node "!!"];
          `Lefta , [ostap ("&&"), make_node "&&"];
          `Nona , [ostap ("<="), make_node "<="; ostap ("<"), make_node "<"; ostap (">="), make_node ">="; ostap (">"), make_node ">"];
          `Nona , [ostap ("=="), make_node "=="; ostap ("!="), make_node "!="];
          `Lefta , [ostap ("+"), make_node "+"; ostap ("-"), make_node "-"];
          `Lefta , [ostap ("*"), make_node "*"; ostap ("/"), make_node "/"; ostap ("%"), make_node "%"];
        |]
        primary
      );
 
      primary: n:DECIMAL {Const n} | x:IDENT {Var x} | -"(" expr -")"
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
    (* loop with a post-condition       *) | Until  of Expr.t * t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) stmt =
      match stmt with
      | Read x -> (match i with
                  | [] -> failwith "Input is empty; nothing to read"
                  | v :: is -> (Expr.update x v s, is, o))
      | Write e -> (s, i, o @ [Expr.eval s e])
      | Assign (x, e) -> (Expr.update x (Expr.eval s e) s, i, o)
      | Seq (st1, st2) -> let (s', i', o') = eval (s, i, o) st1 in 
                          let (s'', i'', o'') = eval (s', i', o') st2 in 
                          (s'', i'', o'')
      | Skip -> (s, i, o)
      | If (c, st, sf) -> if (Expr.eval s c != 0) then eval (s, i, o) st else eval (s, i, o) sf
      | While (c, st) -> if (Expr.eval s c == 0) 
                         then (s, i, o)
                         else eval (eval (s, i, o) st) (While (c, st))
      | Until (c, st) -> let (s', i', o') = eval (s, i, o) st
                         in if (Expr.eval s' c <> 0) 
                            then (s', i', o')
                            else eval (s', i', o') (Until (c, st))
                               
    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT ":=" e:!(Expr.expr) { Assign (x, e) }
      | "read" -"(" x:IDENT -")" { Read x }
      | "write" -"(" e:!(Expr.expr) -")" { Write e }
      | "skip" { Skip }
      | if_stmt
      | "while" c:!(Expr.expr) "do" s:!(stmt) "od" { While (c, s) }
      | "for" s1:!(stmt) -"," c:!(Expr.expr) -"," s2:!(stmt) "do" s:!(stmt) "od" { Seq (s1, While (c, Seq (s, s2))) }
      | "repeat" s:!(stmt) "until" c:!(Expr.expr) { Until (c, s) };

      if_stmt:
        "if" c:!(Expr.expr) "then" s1:!(stmt) "fi" { If (c, s1, Skip) }
      | "if" c:!(Expr.expr) "then" s1:!(stmt) s2:!(else_stmt) "fi" { If (c, s1, s2) };

      else_stmt:
        "else" s:!(stmt) { s }
      | "elif" c:!(Expr.expr) "then" s1:!(stmt) s2:!(else_stmt) { If (c, s1, s2) }
      | "elif" c:!(Expr.expr) "then" s1:!(stmt) { If (c, s1, Skip) };        

      stmt: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun s ss -> Seq (s, ss)) s ss};
      parse: stmt
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
