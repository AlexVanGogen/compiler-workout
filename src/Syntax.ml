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
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
