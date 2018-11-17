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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o, r) as c)) as conf) prg =
  match prg with
  | [] -> conf
  | ins :: ps -> match ins with
                  | BINOP op -> (match stack with
                                | [] -> failwith "Not enough arguments to call binary operation"
                                | x :: [] -> failwith "Not enough arguments to call binary operation"
                                | y :: x :: xs -> eval env (cstack, (Expr.to_func op) x y :: xs, c) ps)
                  | CONST n -> eval env (cstack, n :: stack, c) ps
                  | READ -> (match i with
                            | [] -> failwith "Input is empty; nothing to read"
                            | v :: is -> eval env (cstack, v :: stack, (st, is, o, r)) ps)
                  | WRITE -> (match stack with
                            | [] -> failwith "Stack is empty; nothing to write"
                            | x :: xs -> eval env (cstack, xs, (st, i, o @ [x], r)) ps)
                  | LD x -> eval env (cstack, (State.eval st x) :: stack, c) ps
                  | ST x -> (match stack with
                            | [] -> failwith "Stack is empty; nothing to store"
                            | v :: xs -> eval env (cstack, xs, (Language.State.update x v st, i, o, r)) ps)
                  | LABEL _ -> eval env conf ps
                  | JMP ls -> eval env conf (env#labeled ls)
                  | CJMP (c', ls) -> (match stack with
                                    | [] -> conf
                                    | x :: xs -> if ((c' = "z") = (x = 0))
                                                 then eval env (cstack, xs, c) (env#labeled ls)
                                                 else eval env (cstack, xs, c) ps)
                  | CALL (fname, _, _) -> eval env ((ps, st)::cstack, stack, c) (env#labeled fname)
                  | BEGIN (_, a, l) -> let len = List.length a
                                    in let z = take len stack
                                    in let st' = drop len stack
                                    in let s' = State.enter st (a @ l)
                                    in let s'' = State.update_list a z s'
                                    in eval env (cstack, st', (s'', i, o, r)) ps
                  | _ -> (match cstack with
                           | [] -> ([], stack, c)
                           | (p', s')::cstack -> eval env (cstack, stack, (State.leave st s', i, o, r)) p')

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
  let (_, _, (_, _, o, _)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], None)) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let label_of_int i = Printf.sprintf "L%d" i
  in let label_of_proc fname args = Printf.sprintf "%s__%d" fname (List.length args)
  in
  let rec expr = function
  | Expr.Var   x, l          -> [LD x]
  | Expr.Const n, l          -> [CONST n]
  | Expr.Binop (op, x, y), l -> expr (x, l) @ expr (y, l) @ [BINOP op]
  | Expr.Call (fname, es), l -> (List.concat (List.map (function x -> expr (x, l)) (List.rev es))) @ [CALL (label_of_proc fname es, List.length es, true)]
  in
  let rec compile_with_labels = function
  | Stmt.Seq (s1, s2)  , l -> let (s1_st, s1_l) = compile_with_labels (s1, l)
                              in let (s2_st, s2_l) = compile_with_labels (s2, s1_l)
                              in (s1_st @ s2_st, s2_l)
  | Stmt.Read x        , l -> [READ; ST x], l
  | Stmt.Write e       , l -> expr (e, l) @ [WRITE], l
  | Stmt.Assign (x, e) , l -> expr (e, l) @ [ST x], l
  | Stmt.Skip          , l -> [], l
  | Stmt.If (c, st, sf), l -> let c_st = expr (c, l)
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
  | Stmt.While (c, s)  , l -> let c_st = expr (c, l)
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
  | Stmt.Repeat (s, c) , l -> let c_st = expr (c, l)
                              in let (loop_st, end_l) = compile_with_labels (s, l + 1)
                              in let loop_beginning_label_name = label_of_int l
                              in let end_label_name = label_of_int end_l
                              in (
                                [LABEL loop_beginning_label_name]
                              @ loop_st
                              @ c_st
                              @ [CJMP ("nz", end_label_name);
                                 JMP loop_beginning_label_name;
                                 LABEL end_label_name]
                              , end_l + 1)
  | Stmt.Call (s, es)  , l -> (List.concat (List.map (function x -> expr (x, l)) (List.rev es))
                              @ [CALL (label_of_proc s es, List.length es, false)], l)
  | Stmt.Return None   , l -> [RET false], l
  | Stmt.Return (Some ret), l -> (expr (ret, l)) @ [RET true], l
  in function | (defs, s) -> let (st, lbl) = compile_with_labels (s, 0)
                             in let code =
                                st
                              @ [END]
                              @ List.concat (List.map (fun (fname, (a, l, stmt)) -> let (st', lbl') = compile_with_labels (stmt, lbl) in
                                [
                                  LABEL (label_of_proc fname a);
                                  BEGIN (fname, a, l)
                                ]
                                @ st'
                                @ [END]) defs)
  in code