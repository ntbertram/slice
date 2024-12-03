open Cakes.Main
open Cakes.Basic
open Cakes.Valuation_examples
open Format

let exp_eval abbrvs e_file =
    let e = build_expression abbrvs e_file in
    value_formatter std_formatter (evaluate e default_valuations);
    pp_print_space std_formatter ()


let () =
    match Array.length Sys.argv with
    | 3 -> exp_eval [ Sys.argv.(1) ] Sys.argv.(2)
    | 2 -> exp_eval [] Sys.argv.(1)
    | 1 ->  failwith "No expression file supplied!"
    | _ -> failwith "Too many arguments supplied!"


(* To use:
    dune exec exec/evaluator.exe [abbreviations] [protocol]
*)
