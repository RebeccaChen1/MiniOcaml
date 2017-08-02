(* 
			 CS 51 Final Project
			MiniML -- Expressions
			     Spring 2017
*)

(* Abstract syntax of MiniML expressions *)
open Printf ;;

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;
      
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
 and varid = string ;;
  
(* Sets of varids *)
module SS = Set.Make (struct
		       type t = varid
		       let compare = String.compare
		     end ) ;;

type varidset = SS.t ;;

(* Test to see if two sets have the same elements (for
    testing purposes) *)
let same_vars = SS.equal ;;

(* Generate a set of variable names from a list of strings (for
    testing purposes) *)
let vars_of_list = SS.of_list ;;
  
(* Return a set of the variable names free in [exp] *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var varid -> SS.singleton varid
  | Conditional (exp1, exp2, exp3) -> 
      SS.union (SS.union (free_vars exp1) (free_vars exp2)) (free_vars exp3)
  | Unop (_unp, exp1) -> free_vars exp1           
  | Binop (_binp, exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2) 
  (* removes defined instances of id from the set*) 
  | Fun (id, exp) -> SS.diff (free_vars exp) (SS.singleton id)               
  | Let (id, exp1, exp2) -> SS.union (free_vars exp1) 
                            (SS.diff (free_vars exp2) (SS.singleton id))
  | Letrec (id, exp1, exp2) -> SS.diff (SS.union (free_vars exp1) 
                               (free_vars exp2)) (SS.singleton id)
  | App (exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2)
  | Num _ | Bool _ | Raise | Unassigned -> SS.empty ;;
  
(* Return a fresh variable, constructed with a running counter a la
    gensym. Assumes no variable names use the prefix "var". *)
let ctr = ref 0 ;;
let new_varname () : varid =
  let v = "x" ^ string_of_int (!ctr) in
    ctr := !ctr + 1;
    v ;;
  
(* Substitute [repl] for free occurrences of [var_name] in [exp] *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let fvars = free_vars repl in
  match exp with
  | Var id -> if id = var_name then repl else exp                    
  | Unop (unp, e) -> Unop(unp, subst var_name repl e)              
  | Binop (bnp, e1, e2) -> Binop(bnp, subst var_name repl e1, 
                           subst var_name repl e2)        
  | Conditional (e1, e2, e3) -> Conditional(subst var_name repl e1, 
                                            subst var_name repl e2, 
                                            subst var_name repl e3)   
  | Fun (id, e) -> 
    (* if id = var_name then no substitution *)
    if id = var_name then exp
    (* if id is a freevar, replaces instances of id with fresh var *) 
    else if SS.mem id fvars 
    then let newvar = new_varname () in 
           Fun(newvar, subst var_name repl (subst id (Var(newvar)) e))
    (* normal substitution *) 
    else Fun(id, subst var_name repl e) 
  (* similar to comments in Fun *)               
  | Let (id, e1, e2) -> 
    if id = var_name 
    then Let (id, subst var_name repl e1, e2)
    else if SS.mem id fvars 
         then let newvar = new_varname () in
                Let (newvar, subst var_name repl e1, 
                     subst var_name repl (subst id (Var(newvar)) e2))  
         else Let (id, subst var_name repl e1, subst var_name repl e2) 
  (* if id != var_name, subst e1 and e2 *)
  | Letrec (id, e1, e2) -> 
    if id = var_name then exp 
    else Letrec(id, subst var_name repl e1, subst var_name repl e2)                        
  | App (e1, e2) -> App (subst var_name repl e1, subst var_name repl e2)
  | Num _ | Bool _ | Raise | Unassigned -> exp ;; 

(* exp_to_string -- Returns a string representation of the expr *)
let rec exp_to_string (exp : expr) : string =
  let binop_helper binp =
    match binp with
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Equals -> "="
    | LessThan -> "<"
  in 
  match exp with
  | Var id -> id                    
  | Num x -> sprintf "%d" x        
  | Bool b -> string_of_bool b  
  | Unop (_u, e) -> sprintf "-%s" (exp_to_string e)             
  | Binop (bnp, e1, e2) -> sprintf "%s %s %s" (exp_to_string e1) 
                           (binop_helper bnp) (exp_to_string e2)  
  | Conditional (e1, e2, e3) -> sprintf "if %s then %s else %s" 
                                (exp_to_string e1) 
                                (exp_to_string e2)
                                (exp_to_string e3) 
  | Fun (id, e) -> sprintf "fun %s -> %s" id (exp_to_string e)
  | Let (id, e1, e2) -> sprintf "let %s = %s in %s" id 
                        (exp_to_string e1) (exp_to_string e2)
  | Letrec (id, e1, e2) -> sprintf "let rec %s = %s in %s" id 
                           (exp_to_string e1) (exp_to_string e2)
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"               
  | App (e1, e2) -> sprintf "%s %s" (exp_to_string e1) (exp_to_string e2) ;;

(* exp_to_abstract_string: Returns a string representation of the abstract
   syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  let binop_helper binp = 
    match binp with
    | Plus -> "Binop(+"  
    | Minus -> "Binop(-"
    | Times -> "Binop(*"
    | Equals -> "Binop(="
    | LessThan -> "Binop(<"
  in
  match exp with
  | Var id -> "Var(" ^ id ^ ")"                     
  | Num x -> "Num(" ^ (string_of_int x) ^ ")"                          
  | Bool b -> string_of_bool b                    
  | Unop (_u, e) -> "Unop(~-, " ^ exp_to_abstract_string e ^ ")"              
  | Binop (b, e1, e2) -> binop_helper b ^ ", " ^ exp_to_abstract_string e1 
                         ^ ", " ^ exp_to_abstract_string e2 ^ ")"    
  | Conditional (e1, e2, e3) -> "Conditional(" ^ exp_to_abstract_string e1
                                   ^ ", " ^ exp_to_abstract_string e2 ^
                                   ", " ^ exp_to_abstract_string e3 ^ ")" 
  | Fun (id, e) ->  "Fun(" ^ id ^ ", " ^ exp_to_abstract_string e ^ ")"         
  | Let (id, e1, e2) -> "Let(" ^ id ^ ", " ^ exp_to_abstract_string e1 ^ ", " 
                        ^ exp_to_abstract_string e2 ^ ")"          
  | Letrec (id, e1, e2) -> "Letrec(" ^ id ^ ", " ^ exp_to_abstract_string e1 
                           ^ "," ^ exp_to_abstract_string e2 ^ ")" 
  | Raise -> "Raise"                              
  | Unassigned -> "Unassigned"      
  | App (e1, e2) -> "App(" ^ exp_to_abstract_string e1 ^ ", " 
                    ^ exp_to_abstract_string e2 ^ ")" ;;
