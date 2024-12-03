open Main

(* Expressions for protocols *)
let _ = print_endline "Cut-choose"
let cc_e = build_expression [ "./examples/abb.prtcl" ] "./examples/envy_free_examples/cut-choose.prtcl"
(* Evaluation testing *)

(* let _ =
   let v = evaluate scs_e test_evals test_marks in
   print_endline (Basic.value_to_str v) *)

(* Should equal ([1/6, 1], [1/12, 1/6], [0, 1/12]) *)
(* Type checking *)
open Types

let _ = print_endline "Cut-choose"
let _ = print_endline (typ_to_str (typ_of_exp [] cc_e))
(*
let _ = print_endline "Surplus"
let _ = print_endline (typ_to_str (typ_of_exp [] surplus_e))
*)
(* let _ = print_endline "Trimmings3" *)

(* let _ = print_endline (typ_to_str (typ_of_exp [] tr_e)) *)
(*
let _ = print_endline "Selfridge-Conway 1"
let _ = print_endline (typ_to_str (typ_of_exp [] sc_e))
let _ = print_endline "Waste-makes-haste 3"
let _ = typ_of_exp [] h3_e
let _ = print_endline "Selfridge-Conway 2"
let _ = typ_of_exp [] scunion_e
*)
(* let _ = typ_of_exp [] scs_e
   let _ = typ_of_exp [] scf_e *)

(* Path testing *)
open Path

let cc_paths = expression_to_path_list cc_e

open Expression_to_formula

let c, rho, k, divides = closed_cnstr (List.hd cc_paths)
let cc_formulas = List.map (fun p -> build_path_formula p) cc_paths

(*let cc_constraint = complete_constraint cc_e*)
open Properties

let cc_envy = check_property cc_e (envy_any 2)

open Formula

let _ = print_formula cc_envy
let cc_path1 = List.hd cc_paths
let cc_path1_formula = build_path_formula cc_path1
let surplus_e = build_expression [ "./examples/abb.prtcl" ] "./examples/envy_free_examples/surplus.prtcl"

let _ = print_endline "Reg formula"
let f = build_path_formula_with_f_no_red cc_path1 (fun _ -> True)
let _ = print_formula f

(* let temp1_e = build_expression [ "./examples/abb.prtcl" ] "./examples/temp1.prtcl" *)
(* let _ = print_endline "Trmmings3"
   let tr_e = build_expression [ "./examples/abb.prtcl" ] "./examples/trm.prtcl" *)

(*
   let ccwrong_e = build_expression ["./examples/abb.prtcl"] "./examples/ccwrong.prtcl"
   *)

(* let sc_paths = expression_to_path_list sc_e
   let (sc_c, sc_rho, sc_k, sc_divides) = cnstr (hd sc_paths, []) [] [] *)

(* let _ = print_endline "SC formula" *)
(*let sc_f100 = build_path_formula (nth sc_paths 595)*)

(*let _ = print_formula sc_f100*)

(*let sc_f = complete_real_constraint sc_e *)

(*
   let am3_e = build_expression ["./examples/abb.prtcl"] "./examples/am3new.prtcl"
   let am4_e = build_expression ["./abbam4.prtcl"] "./examples/am4algo3.prtcl"
   *)
