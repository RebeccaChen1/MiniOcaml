open Expr ;;
open Evaluation ;;
open Miniml ;;

let e1 = Var("x") ;;	
let e2 = Num(1) ;;
let e3 = Bool(true) ;;
let e4 = Binop(Plus, Num(3), Num(4)) ;;
let e5 = Binop(Equals, Num(2), Num(3)) ;;
let e6 = Unop(Negate, Num(1)) ;;
let e7 = Conditional(Binop(Equals, Num(5), Num(5)), Num(0), Num(1)) ;;
let e8 = Fun("x", Binop(Plus, Var("x"), Num(5))) ;;
let e9 = Fun("x", Binop(Plus, Var("x"), Var("y"))) ;; 
let e10 = Let("x", Num(5), Binop(Plus, Var("x"), Var("y"))) ;;
let e11 = Let("x", Num(1), Let("f", Fun("y", Binop(Plus, Var("x"), 
	      Var("y"))), Let("x", Num(2), App(Var("f"), Num(3))))) ;;
let e12 = Letrec("f", Fun("x", Conditional(Binop(Equals, Var("x"), Num(0)), 
	      Var("x"), App(Var("f"), Binop(Minus, Var("x"), Num(1))))), 
          App(Var("f"), Num(2))) ;;
let e13 = App(Fun("x", Binop(Plus, Var("x"), Num(5))), Num(5)) ;;
let e14 = Let("g", Fun("y", Binop(Plus, Var("y"), 
	      Num(2))), App(Var("g"), Num(0))) ;;
let e15 = Let("x", Num(5), Binop(Plus, Var("x"), Var("x"))) ;;
let e16 = Fun ("x", Binop(Plus, Var("x"), Num(5))) ;;
let e17 = Fun ("y", Binop(Plus, Var("x"), Var("y"))) ;;
let e18 = Letrec("f", Fun("x", Conditional(Binop(Equals, Var("x"), Num(0)), 
	      Binop(Plus, Var("x"), Var("y")), App(Var("f"), 
          Binop(Minus, Var("x"), Num(1))))), App(Var("f"), Num(2))) ;;

(* expr tests *)
let test_exp_to_abstract_string () =
	assert (exp_to_abstract_string e1 = "Var(x)") ;
	assert (exp_to_abstract_string e2 = "Num(1)") ;
	assert (exp_to_abstract_string e3 = "true") ;
	assert (exp_to_abstract_string e15 = 
		   "Let(x, Num(5), Binop(+, Var(x), Var(x)))") ;
	assert (exp_to_abstract_string e16 = "Fun(x, Binop(+, Var(x), Num(5)))") ;
() ;;

let test_exp_to_string () =
	assert (exp_to_string e15 = "let x = 5 in x + x") ;
	assert (exp_to_string e16 = "fun x -> x + 5") ;
() ;;

let test_subst () =
	assert (subst ("x") (Num(10)) e16 = e16) ;
	assert (subst ("x") (Num(10)) e17 = 
		    Fun("y", Binop(Plus, Num(10), Var("y")))) ;
    assert (subst ("y") (Num(1)) e18 =
            Letrec("f", Fun("x", Conditional(Binop(Equals, Var("x"), Num(0)), 
	        Binop(Plus, Var("x"), Num(1)), App(Var("f"), Binop(Minus, Var("x"), Num(1))))), 
            App(Var("f"), Num(2)))) ;
    assert (subst ("y") (Num(1)) e9 = 
            Fun("x", Binop(Plus, Var("x"), Num(1)))) ;
    assert (subst ("y") (Num(1)) e10 =
            Let("x", Num(5), Binop(Plus, Var("x"), Num(1)))) ;
    assert (subst ("x") (Num(1)) e9 =
            Fun("x", Binop(Plus, Var("x"), Var("y")))) ;
    assert (subst ("x") (Num(1)) e10 = 
            Let("x", Num(5), Binop(Plus, Var("x"), Var("y")))) ; 
() ;;

let test_free_vars () =
    let ex1 = Let("x", Num(5), Binop(Minus, Var("x"), Var("y"))) in
    let ex2 = Let("x", Num(5), Binop(Times, Var("z"), Var("y"))) in
	assert (same_vars (free_vars e16) (vars_of_list [])) ;
	assert (same_vars (free_vars (Binop (Plus, Num(3), Num(4)))) 
		              (vars_of_list [])) ;
	assert (same_vars (free_vars ex1) (vars_of_list ["y"])) ;
	assert (same_vars (free_vars ex2) (vars_of_list ["y";"z"])) ;
() ;;


(* evaluation tests *)
let env0 = Env.create () ;;

let close_test () = 
  assert(Env.close e1 env0 = Closure(e1, env0)) ;
() ;;

let lookup_test () = 
  let e_env = Env.extend env0 "x" (ref(Env.Val (Num(5)))) in
  assert(Env.lookup e_env "x" = Env.Val (Num(5))) ;  
() ;;

let extend_test () =
  let e_env = Env.extend env0 "x" (ref(Env.Val (Num(5)))) in
  let e_env2 = Env.extend e_env "x" (ref(Env.Val (Num(10)))) in
  let e_env3 = Env.extend e_env2 "y" (ref(Env.Val (Num(5)))) in
  assert(Env.env_to_string e_env = "[(x, Val(Num(5)));]") ; 
  assert(Env.env_to_string e_env2 = "[(x, Val(Num(10)));]") ;
  assert(Env.env_to_string e_env3 = "[(x, Val(Num(10)));(y, Val(Num(5)));]") ;
() ;;

let eval_s_test () =
  (* e11 evaluates differently in eval_s than in eval_d *)
  assert(eval_s e11 env0 = Env.Val (Num(4))) ;
  assert(eval_s e2 env0 = Env.Val (Num(1))) ;
  assert(eval_s e3 env0 = Env.Val (Bool(true))) ;
  assert(eval_s e4 env0 = Env.Val (Num(7))) ; 
  assert(eval_s e5 env0 = Env.Val (Bool(false))) ;
  assert(eval_s e6 env0 = Env.Val (Num(-1))) ;
  assert(eval_s e7 env0 = Env.Val (Num(0))) ;
  assert(eval_s e8 env0 = Env.Val (Fun("x", Binop(Plus, Var("x"), Num(5))))) ;
  assert(eval_s e12 env0 = Env.Val (Num(0))) ;
  assert(eval_s e13 env0 = Env.Val (Num(10))) ;
  assert(eval_s e14 env0 = Env.Val (Num(2))) ;
() ;;

let eval_d_test () = 
  (* e11 evaluates to 5 in eval_d and to 4 in eval_s and eval_l *)
  assert(eval_d e11 env0 = Env.Val (Num(5))) ;
  assert(eval_d e2 env0 = Env.Val (Num(1))) ;
  assert(eval_d e3 env0 = Env.Val (Bool(true))) ;
  assert(eval_d e4 env0 = Env.Val (Num(7))) ; 
  assert(eval_d e5 env0 = Env.Val (Bool(false))) ;
  assert(eval_d e6 env0 = Env.Val (Num(-1))) ;
  assert(eval_d e7 env0 = Env.Val (Num(0))) ;
  assert(eval_d e8 env0 = Env.Val (Fun("x", Binop(Plus, Var("x"), Num(5))))) ;
  assert(eval_d e12 env0 = Env.Val (Num(0))) ;
  assert(eval_d e13 env0 = Env.Val (Num(10))) ;
  assert(eval_d e14 env0 = Env.Val (Num(2))) ;
() ;;

let eval_l_test () =
  assert(eval_l e11 env0 = Env.Val (Num(4))) ;
  assert(eval_l e2 env0 = Env.Val (Num(1))) ;
  assert(eval_l e3 env0 = Env.Val (Bool(true))) ;
  assert(eval_l e4 env0 = Env.Val (Num(7))) ; 
  assert(eval_l e5 env0 = Env.Val (Bool(false))) ;
  assert(eval_l e6 env0 = Env.Val (Num(-1))) ;
  assert(eval_l e7 env0 = Env.Val (Num(0))) ;
  assert(eval_l e8 env0 = 
  	     Env.Closure (Fun("x", Binop(Plus, Var("x"), Num(5))), env0));
  assert(eval_l e12 env0  = Env.Val (Num(0))) ;
  assert(eval_l e13 env0 = Env.Val (Num(10))) ;
  assert(eval_l e14 env0 = Env.Val (Num(2))) ;
() ;;

test_exp_to_abstract_string () ;;
test_exp_to_string () ;;
test_subst () ;;
test_free_vars () ;;

close_test () ;;
lookup_test () ;;
extend_test () ;;
eval_s_test () ;;
eval_d_test () ;;
eval_l_test () ;;



