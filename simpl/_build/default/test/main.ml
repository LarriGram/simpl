open OUnit2
open Interp
open Ast
open Main

(** [make_p name ast str] makes an OUnit test named [name] that expects
    [str] to parse to [ast]. *)
    let make_p name ast str =
      [name >:: (fun _ -> assert_equal ast (parse str));]
     
  let make_i n i s =
    [n >:: (fun _ -> assert_equal (Int i) (interp_small s));
     n >:: (fun _ -> assert_equal (Int i) (interp_big s))]
  
  let make_f n i s =
    [n >:: (fun _ -> assert_equal (Float i) (interp_small s));
     n >:: (fun _ -> assert_equal (Float i) (interp_big s))]
  
  (** [make_b n b s] makes an OUnit test named [n] that expects
      [s] to evalute to [Bool b]. *)
  let make_b n b s =
    [n >:: (fun _ -> assert_equal (Bool b) (interp_small s));
     n >:: (fun _ -> assert_equal (Bool b) (interp_big s))]
  
  (** [make_t n s] makes an OUnit test named [n] that expects
      [s] to fail type checking with error string [s']. *)
  let make_t n s' s =
    [n >:: (fun _ -> assert_raises (Failure s') (fun () -> interp_small s));
     n >:: (fun _ -> assert_raises (Failure s') (fun () -> interp_big s))]
  

let int_num_tests = [
  (* Numeric parsing tests *)
  make_p "parse_int" (Int 1) "1";
  make_p "parse_neg" (Int ~-1) "-1";
  make_p "parse_add" (Binop (Add, Int 1, Int 70)) "1 + 70";
  make_p "parse_leq" (Binop (Leq, Int 0, Int ~-1)) ("0 <= -1");
  make_p "parsing_leq_var" (Binop(Leq, Var "hello",  Var  "World"))    "hello <= World";
  make_p "parsing_if" (If (Var "x", Var "y", Int 10)) "if x  then y  else 10";
  make_p "parse_power" (Binop (Power, Int 1, Int 70)) "1 ** 70";
 
]

let int_let_if_tests = [
  (* Integer evaluation tests *)
  make_i "int" 22 "22";
  make_i "add" 22 "11+11";
  make_i "adds" 22 "(10+1)+(5+6)";
  make_i "let" 22 "let x=22 in x";
  make_i "lets" 22 "let x = 0 in let x = 22 in x";
  make_i "mul1" 22 "2*11";
  make_i "mul2" 22 "2+2*10";
  make_i "mul3" 14 "2*2+10";
  make_i "mul4" 40 "2*2*10";
  make_i "if1" 22 "if true then 22 else 0";
  make_i "if2" 22 "if 1+2 <= 3+4 then 22 else 0";
  make_i "if3" 22 "if 1+2 <= 3*4 then let x = 22 in x else 0";
  make_i "letif" 22 "let x = 1+2 <= 3*4 in if x then 22 else 0";
]

let bool_tests = [
  (* Boolean evaluation tests *)
  make_b "true" true "true";
  make_b "leq" true "1<=1";
]

let type_tests = [
  (* Type checking tests *)
  make_t "ty plus" bop_err "1 + true";
  make_t "ty mult" bop_err "1 * false";
  make_t "ty leq" bop_err "true <= 1";
  make_t "if guard" if_guard_err "if 1 then 2 else 3";
  make_t "if branch" if_branch_err "if true then 2 else false";
  make_t "unbound" unbound_var_err "x";
  make_t "ty power" bop_err "1 ** false";
]

let float_tests = [
  (* Float evaluation tests *)
  make_f "let" 22.2 "let x=22.2 in x";
  make_f "addf" 2.2 "1.1 +. 1.1";
  make_f "mulf1" 22.0 "2.0 *. 11.0";
  make_f "mulf2" 22.0 "2.0+.2.0*.10.0";
  make_f "mul3" 14.0 "2.0*.2.0+.10.0";
  make_p "parse_float" (Float 1.1) "1.1";
  make_p "parse_neg_float" (Float ~-.1.1) "-1.1";
  make_p "parse_addf" (Binop (Addf, Float 1.1, Float 70.7)) "1.1 +. 70.7";
  make_p "parse_powerf" (Binop (Powerf, Float 1.1, Float 70.1)) "1.1 **. 70.1";
  make_f "if1" 22.0 "if true then 22.0 else 0.0";

]

let all_tests = int_num_tests @ int_let_if_tests @ bool_tests @ type_tests @ float_tests

let _ = run_test_tt_main ("suite" >::: List.flatten all_tests)
