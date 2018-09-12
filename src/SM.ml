open GT       
       
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
let rec eval (st, (s, i, o)) p =
  match p with
  | [] -> (st, (s, i, o))
  | ins :: ps -> match ins with
                    | BINOP op -> (match st with
                                  | [] -> failwith "Not enough arguments to call binary operation"
                                  | x :: [] -> failwith "Not enough arguments to call binary operation"
                                  | y :: x :: xs -> eval ((Syntax.Expr.eval s (Binop (op, Const x, Const y))) :: xs, (s, i, o)) ps)
                    | CONST n -> eval (n :: st, (s, i, o)) ps
                    | READ -> (match i with
                              | [] -> failwith "Input is empty; nothing to read"
                              | v :: is -> eval (v :: st, (s, is, o)) ps)
                    | WRITE -> (match st with
                               | [] -> failwith "Stack is empty; nothing to write"
                               | x :: xs -> eval (xs, (s, i, o @ [x])) ps)
                    | LD x -> eval (s x :: st, (s, i, o)) ps
                    | ST x -> match st with
                              | [] -> failwith "Stack is empty; nothing to store"
                              | v :: xs -> eval (xs, (Syntax.Expr.update x v s, i, o)) ps

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExpr e =
  match e with
  | Syntax.Expr.Const n -> [CONST n]
  | Syntax.Expr.Var x -> [LD x]
  | Syntax.Expr.Binop (op, e1, e2) -> compileExpr e1 @ compileExpr e2 @ [BINOP op]
 
let rec compile stmt =
  match stmt with
  | Syntax.Stmt.Read x -> [READ; ST x]
  | Syntax.Stmt.Write e -> compileExpr e @ [WRITE]
  | Syntax.Stmt.Assign (x, e) -> compileExpr e @ [ST x]
  | Syntax.Stmt.Seq (st1, st2) -> compile st1 @ compile st2
