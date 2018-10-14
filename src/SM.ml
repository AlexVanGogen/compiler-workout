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
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* let f = open_out "file.txt"
let print_insn ins = match ins with
  | BINOP s -> Printf.fprintf f "BINOP %s\n" s
  | CONST i -> Printf.fprintf f "CONST %d\n" i
  | READ -> Printf.fprintf f "READ\n"
  | WRITE -> Printf.fprintf f "WRITE\n"
  | LD s -> Printf.fprintf f "LOAD %s\n" s
  | ST s -> Printf.fprintf f "STORE %s\n" s
  | LABEL s -> Printf.fprintf f "LABEL %s\n" s
  | JMP s -> Printf.fprintf f "JUMP %s\n" s
  | CJMP (s1, s2) -> Printf.fprintf f "JUMPIF %s %s\n" s1 s2
  | BEGIN (a, l) -> Printf.fprintf f "BEGIN (%d %d)\n" (List.length a) (List.length l)
  | END -> Printf.fprintf f "END\n"
  | CALL fname -> Printf.fprintf f "CALL %s\n" fname *)

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (cst, st, (s, i, o)) p =
  match p with
  | [] -> (cst, st, (s, i, o))
  | ins :: ps -> match ins with
                    | BINOP op -> (match st with
                                  | [] -> failwith "Not enough arguments to call binary operation"
                                  | x :: [] -> failwith "Not enough arguments to call binary operation"
                                  | y :: x :: xs -> eval env (cst, (Expr.eval s (Expr.Binop (op, Expr.Const x, Expr.Const y))) :: xs, (s, i, o)) ps)
                    | CONST n -> eval env (cst, n :: st, (s, i, o)) ps
                    | READ -> (match i with
                              | [] -> failwith "Input is empty; nothing to read"
                              | v :: is -> eval env (cst, v :: st, (s, is, o)) ps)
                    | WRITE -> (match st with
                               | [] -> failwith "Stack is empty; nothing to write"
                               | x :: xs -> eval env (cst, xs, (s, i, o @ [x])) ps)
                    | LD x -> eval env (cst, (State.eval s x) :: st, (s, i, o)) ps
                    | ST x -> (match st with
                              | [] -> failwith "Stack is empty; nothing to store"
                              | v :: xs -> eval env (cst, xs, (Language.State.update x v s, i, o)) ps)
                    | LABEL _ -> eval env (cst, st, (s, i, o)) ps
                    | JMP ls -> eval env (cst, st, (s, i, o)) (env#labeled ls)
                    | CJMP (c, ls) -> (match st with
                                      | [] -> (cst, st, (s, i, o))
                                      | x :: xs -> if ((c = "z") = (x = 0))
                                                   then eval env (cst, st, (s, i, o)) (env#labeled ls)
                                                   else eval env (cst, st, (s, i, o)) ps)
                    | BEGIN (a, l) -> let len = List.length a
                                      in let z = take len st
                                      in let st' = drop len st
                                      in let s' = State.push_scope s (a @ l)
                                      in let s'' = bimap (fun x v -> State.update v x s') z a s'
                                      in eval env (cst, st', (s'', i, o)) ps
                    | END -> (match cst with
                             | [] -> ([], st, (s, i, o))
                             | (p', s')::cst -> eval env (cst, st, (State.drop_scope s s', i, o)) p')
                    | CALL fname -> eval env ((ps, s)::cst, st, (s, i, o)) (env#labeled fname)

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
let label_of_int i = Printf.sprintf "L%d" i
in let label_of_proc fname args = Printf.sprintf "%s#%d" fname (List.length args)
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
| Stmt.Repeat (s, c) , l -> let c_st = expr c
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
| Stmt.Call (s, es)  , l ->  (List.concat (List.map expr es)
                            @ [CALL (label_of_proc s es)], l)
in function | (defs, s) -> let (st, lbl) = compile_with_labels (s, 0)
                           in let code =
                            List.concat (List.map (fun (fname, (a, l, stmt)) -> let (st', lbl') = compile_with_labels (stmt, lbl) in
                              [JMP "MAIN";
                               LABEL (label_of_proc fname a);
                               BEGIN (a, l)]
                            @ st'
                            @ [END]) defs)
                            @ [LABEL "MAIN"]
                            @ st
                           in code