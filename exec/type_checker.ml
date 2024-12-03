open Cakes.Main
open Cakes.Types

(*OCAMLRUNPARAM=b dune exec exec/type_checker.exe [args] *)
let () =
  let abbrv, prtcl =
    match Array.length Sys.argv with
    | 3 -> ([ Sys.argv.(1) ], Sys.argv.(2))
    | 2 -> ([], Sys.argv.(1))
    | 1 -> failwith "No file arguments provided"
    | _ -> failwith "Too many arguments provided"
  in
  let e = build_expression abbrv prtcl in
  print_endline (typ_to_str (typ_of_exp [] e))
