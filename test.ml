open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Types
open Expr

let is_osx = Conf.make_bool "osx" false "Set this flag to run on osx";;

let t name program expected = name>::test_run program name expected;;

let ta name program expected = name>::test_run_anf program name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;

(*let tfvs name program expected = name>::*)
  (*(fun _ ->*)
    (*let ast = parse_string name program in*)
    (*let anfed = anf (tag ast) in*)
    (*let vars = free_vars anfed in*)
    (*let c = Pervasives.compare in*)
    (*let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in*)
    (*assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print)*)
(*;;*)

(*let tanf name program expected = name>::fun _ ->*)
  (*assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;*)

(*let teq name actual expected = name>::fun _ ->*)
  (*assert_equal expected actual ~printer:(fun s -> s);;*)

let tests = [
  t "m1" "5 - 5" "0";
  t "m2" "5 + 5" "10";
  t "m3" "5 * 5" "25";
  t "m4" "5 - 0" "5";
  t "m5" "5 + 0" "5";
  t "m6" "5 * 0" "0";
  t "m7" "let x = 5 in x" "5";
  t "m8" "let x = 5, y = 6 in x + y" "11";
  t "m9" "let x = 5 + 6 in x" "11";
  t "m10" "let x = let y = 5 + 6 in y in x - 6" "5";
  t "m11" "let x = 5 in let y = 5 + x in y" "10";
  t "m12" "let x = 5, y = 6 in let z = x + y in z" "11";
  t "m13" "let x = 5, y = 6 in let z = let a = x + y in a in z" "11";
  t "m14" "let x = 5 in 5 * x" "25";
  t "m15" "let x = 5, y = 6 in x * y" "30";
  t "m16" "let x = 5, y = 6 in let z = let a = x * y in a in z" "30";
]

let suite =
"suite">:::tests

let () =
  run_test_tt_main suite
;;

