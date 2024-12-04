open Main
(* top-level test file *)

(* Expressions for protocols *)
let _ = print_endline "Cut-choose expression building"
let cutchoose = build_expression [ "./examples/abb.prtcl" ] "./examples/envy_free_examples/cut-choose.prtcl"
let selfridgeconwaysurplus = build_expression [ "./examples/abb.prtcl" ] "./examples/envy_free_examples/selfridge-conway-surplus.prtcl"
(* Evaluation testing *)

let _ = print_endline "Cut-choose evaluation"
open Valuation_examples
let _ = print_endline (Basic.value_to_str (evaluate cutchoose default_valuations)) 
(* Should equal ([0, 11/32], [11/32, 1]) *)

(* Type checking *)
let _ = print_endline "Cut-choose type checking"
open Types

let _ = print_endline "Type of Cut-choose"
let _ = print_endline (typ_to_str (typ_of_exp [] cutchoose))
(* Should equal Piece * Piece *)

(* Path testing *)
let _ = print_endline "Cut-choose path building"
open Path

let cutchoose_paths = expression_to_path_list cutchoose

let _ = print_endline "Cut-choose formula translation"
open Expression_to_formula

let c, rho, k, divides = closed_cnstr (List.hd cutchoose_paths)
let cutchoose_path_formulas = List.map (fun p -> build_path_formula true p) cutchoose_paths

open Properties
let cutchoose_envy_formula = verification true cutchoose envy_any

open Formula
let _ = print_formula cutchoose_envy_formula
