open Cakes.Solve
open Cakes.Main
open Cakes.Path
open Cakes.Properties

(*OCAMLRUNPARAM=b dune exec exec/solver.exe [ABBREVIATION FILE] [PROTOCOL FILE] [ADDITIONAL ARGUMENTS] *)

(* Given a string and potentially an index, will print the the string in the file with the corresponding index name*)
(* let print_formula i smt_formula =
   match i with
   | Some i -> string_to_file smt_formula ("smt/" ^ string_of_int i ^ ".smt2")
   | None -> string_to_file smt_formula "solve.smt2" *)

(* let default_op =
   (* get_solve_from_file_new () *)
   let s =
     get_solve_from_file_old
       (fun x -> x)
       [ (*Sys.argv.(3)*) ]
       (*Sys.argv.(4)*) (fun x -> x)
   in
   let s' = s ^ "(check-sat)" in
   string_to_file s' "solve.smt2" *)

(* let second_op () = solve_from_file_in_place () *)


let print_num_paths e =
  print_string "Number of paths: ";
  print_endline (e |> num_paths |> string_of_int)


let () =
  try
    let e = build_expression [ Sys.argv.(1) ] Sys.argv.(2) in
    match Sys.argv.(3) with
    | "custom" -> produce_smt_file true (custom) e
    | "envy" -> produce_smt_file true (envy_any) e
    | "envy_no_red" -> produce_smt_file false (envy_any) e
    | "paths" -> print_num_paths e
    | "no_prop" -> produce_smt_file true (no_prop) e
    | "large" -> large_envy_free_smt e envy_any
    | _ -> failwith "improper argument"
  with _ -> ()
