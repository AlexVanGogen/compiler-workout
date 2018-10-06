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
let rec eval env (st, (s, i, o)) p =
  match p with
  | [] -> (st, (s, i, o))
  | ins :: ps -> match ins with
                    | BINOP op -> (match st with
                                  | [] -> failwith "Not enough arguments to call binary operation"
                                  | x :: [] -> failwith "Not enough arguments to call binary operation"
                                  | y :: x :: xs -> eval env ((Language.Expr.eval s (Binop (op, Const x, Const y))) :: xs, (s, i, o)) ps)
                    | CONST n -> eval env (n :: st, (s, i, o)) ps
                    | READ -> (match i with
                              | [] -> failwith "Input is empty; nothing to read"
                              | v :: is -> eval env (v :: st, (s, is, o)) ps)
                    | WRITE -> (match st with
                               | [] -> failwith "Stack is empty; nothing to write"
                               | x :: xs -> eval env (xs, (s, i, o @ [x])) ps)
                    | LD x -> eval env (s x :: st, (s, i, o)) ps
                    | ST x -> (match st with
                              | [] -> failwith "Stack is empty; nothing to store"
                              | v :: xs -> eval env (xs, (Language.Expr.update x v s, i, o)) ps)
                    | LABEL _ -> eval env (st, (s, i, o)) ps
                    | JMP ls -> eval env (st, (s, i, o)) (env#labeled ls)
                    | CJMP (c, ls) -> (match st with
                                      | [] -> (st, (s, i, o))
                                      | x :: xs -> if ((c = "z") = (x = 0))
                                                   then eval env (st, (s, i, o)) (env#labeled ls)
                                                   else eval env (st, (s, i, o)) ps)


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
let rec compile =
  let label_of_int i = Printf.sprintf "L%d" i
  in
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec compile_with_labels = function
  | Stmt.Seq (s1, s2)  , l -> let (s1_st, s1_l) = compile_with_labels (s1, l)
                              in let (s2_st, s2_l) = compile_with_labels (s2, s1_l)
                              in (s1_st @ s2_st, s2_l)
  | Stmt.Read x        , l -> [READ; ST x], l
  | Stmt.Write e       , l -> expr e @ [WRITE], l
  | Stmt.Assign (x, e) , l -> expr e @ [ST x], l
  | Stmt.Skip          , l -> [], l
  | Stmt.If (c, st, sf), l -> let c_st = expr c
                              in let (true_st, false_l) = compile_with_labels (st, l + 1)
                              in let (false_st, end_l) = compile_with_labels (sf, false_l + 1)
                              in let false_label_name = label_of_int l
                              in let end_label_name = label_of_int false_l
                              in (
                                c_st 
                              @ [CJMP ("z", false_label_name)]
                              @ true_st
                              @ [JMP end_label_name;
                                 LABEL false_label_name]
                              @ false_st
                              @ [LABEL end_label_name]
                              , end_l)
  | Stmt.While (c, s)  , l -> let c_st = expr c
                              in let (loop_st, end_l) = compile_with_labels (s, l + 1)
                              in let loop_beginning_label_name = label_of_int l
                              in let end_label_name = label_of_int end_l
                              in (
                                [LABEL loop_beginning_label_name]
                              @ c_st
                              @ [CJMP ("z", end_label_name)]
                              @ loop_st
                              @ [JMP loop_beginning_label_name;
                                 LABEL end_label_name]
                              , end_l + 1)
  | Stmt.Until (c, s)  , l -> let c_st = expr c
                              in let (loop_st, end_l) = compile_with_labels (s, l + 1)
                              in let loop_beginning_label_name = label_of_int l
                              in let end_label_name = label_of_int end_l
                              in (
                                [LABEL loop_beginning_label_name]
                              @ loop_st
                              @ c_st
                              @ [CJMP ("nz", end_label_name)]
                              @ [JMP loop_beginning_label_name;
                                 LABEL end_label_name]
                              , end_l + 1)
  in function | s -> let (st, _) = compile_with_labels (s, 0) in st
