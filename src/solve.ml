open Z3

open Formula_to_smtlib

(*open Assumptions*)
(*open Types*)
open Path
open Formula
open Expression_to_formula
open Properties
open Ast
open Main

(*
(* Solving with z3 *)
let solve_from_constraint f =
    let smt = f_to_smt f in
    let solver = Solver.mk_simple_solver ctx in
    (*Solver.add solver assumption_list ;*) let status = Solver.check solver [cz3] in
    (match Solver.get_model solver with
    | Some (m) -> print_endline (Model.to_string m)
    | None -> ()) ;
    print_endline (Solver.string_of_status status)

let solve_from_file prop dl s =
    let c =  prop_and_constraint prop (build_formula dl s) in
    let cz3 = con_to_z3 c in
    let solver = Solver.mk_solver ctx None in
    (*Solver.add solver assumption_list ;*) let status = Solver.check solver [cz3] in
    (match Solver.get_model solver with
    | Some (m) -> print_endline (Model.to_string m)
    | None -> ()) ;
    print_endline (Solver.string_of_status status) ; (let t = ((Solver.get_unsat_core solver)) in print_endline (string_of_int (List.length t)))

let solve_from_file_solver solver prop dl s =
    let c =  prop_and_constraint prop (build_formula dl s) in
    let cz3 = con_to_z3 c in
    (*Solver.add solver assumption_list ;*) let status = Solver.check solver [cz3] in
    (match Solver.get_model solver with
    | Some (m) -> print_endline (Model.to_string m)
    | None -> ()) ;
    print_endline (Solver.string_of_status status) 

*)
(* let get_solve_from_file_old (*prop*) _ (*dl*) _ (*s*) _ =
   let f = check_property am3wrong_e (envy_any 3) in
   let smt = f_to_smt f in
   let solver = Solver.mk_solver ctx None in
   Solver.add solver [ smt ];
   Solver.to_string solver *)

let produce_smt_file red prop (e : expression) =
  let f = verification red e prop in
  let smt = f_to_smt f in
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [ smt ];
  let s = Solver.to_string solver in
  let s = s ^ "(check-sat)" in
  string_to_file s "solve.smt2"


let solve_in_place red prop e =
  let f = verification red e prop in
  let smt = f_to_smt f in
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [ smt ];
  match Solver.check solver [] with
  | SATISFIABLE -> print_endline "sat"
  | UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN -> print_endline "unknown"

let solve_individual_path red p =
  let f = build_path_formula red p envy_any in
  let smt = f_to_smt f in
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [ smt ];
  match Solver.check solver [] with
  | SATISFIABLE -> true
  | UNSATISFIABLE -> false
  | UNKNOWN -> true

(** Given an expression, this functions should test if every branch is satisfiable. *)
let solve_expression (red : bool) (e : expression) (delta : int) =
  let count = ref 0 in
  let pre_path_seq = expression_to_pre_path_seq e in
  let path_seq = pre_path_to_path_seq pre_path_seq in
  let rec helper acc (s : path seq) =
    count := !count + 1;
    if !count mod delta = 0 then print_endline (string_of_int !count) else ();
    if acc = true then true
    else
      match s with
      | Nil -> acc
      | Cons (h, t) -> helper (acc || solve_individual_path red h) (t ())
  in
  if helper false path_seq then "sat" else "unsat"

let formula_to_file f n =
  let smt = f_to_smt f in
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [ smt ];
  let s = Solver.to_string solver ^ "(check-sat)" in
  string_to_file s ("solve" ^ string_of_int n ^ ".smt2")

(* creates an smt2 file for every 200,000 paths *)
let large_envy_free_smt (e : expression) prop =
  let count = ref 0 in
  let curr_file_num = ref 0 in
  let pre_path_seq = expression_to_pre_path_seq e in
  let path_seq = pre_path_to_path_seq pre_path_seq in
  let rec helper acc (s : path seq) : unit =
    count := !count + 1;

    (* print_endline (string_of_int !count); *)

    (* match s with
       | Nil ->
           if acc = [] then ()
           else (
             curr_file_num := !curr_file_num + 1;
             formula_to_file (Or acc) !curr_file_num);
           print_endline ("Done with file " ^ string_of_int !curr_file_num)
       | Cons (h, t) ->
           let f = build_path_formula_with_f h (envy_any n) in
           let acc' = f :: acc in
           if !count mod 20000 = 0 then (
             curr_file_num := !curr_file_num + 1;
             formula_to_file (Or acc') !curr_file_num;
             helper [] (t ()))
           else helper acc' (t ()) *)
    if !count mod 200000 = 0 then (
      curr_file_num := !curr_file_num + 1;
      formula_to_file (Or acc) !curr_file_num;
      helper [] s)
    else
      match s with
      | Nil ->
          curr_file_num := !curr_file_num + 1;
          formula_to_file (Or acc) !curr_file_num;
          print_endline ("Done with file " ^ string_of_int !curr_file_num)
      | Cons (h, t) ->
          let f = build_path_formula true h prop in
          helper (f :: acc) (t ())
  in
  helper [] path_seq

(* let branch_solve _ _ _ =
    let f =  check_property_by_branch h3_e (envy_any 3) in
    let smt = f_to_smt f in
    let solver = Solver.mk_solver ctx None in
    Solver.add solver [smt] ; (Solver.to_string solver) *)

let gen_solver smt =
  let solver = Solver.mk_solver ctx None in
  (*let const = List.init (List.length smt) (fun i -> Boolean.mk_const_s ctx (string_of_int i)) in*)
  (*Solver.add solver const; Solver.assert_and_track_l solver smt const *)
  Solver.add solver smt;
  Solver.to_string solver

let path_solver_from_file e =
  let paths = expression_to_path_list e in
  let complete_formulas =
    map (fun p -> build_path_formula true p envy_any) paths
  in
  let smts = map and_to_sep complete_formulas in
  map gen_solver smts
