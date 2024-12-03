open Ast
open Out_channel

(* Parsing files *)
open Lexing
module I = Parser.MenhirInterpreter

let succeed pre_exp = Ok pre_exp

let fail lexbuf (_ : 'a I.checkpoint) =
  Error
    (Printf.sprintf "syntax error: " ^ msg_from_info (Lexer.info_of_buf lexbuf))

let loop lexbuf result =
  let supplier = I.lexer_lexbuf_to_supplier Lexer.read lexbuf in
  I.loop_handle succeed (fail lexbuf) supplier result

(* Parsing a string to a pre_exp and list of definitions *)
let process (line : string) =
  let lexbuf = from_string line in
  try loop lexbuf (Parser.Incremental.prog lexbuf.lex_curr_p)
  with Lexer.LexingError e ->
    failwith (snd e ^ " " ^ (e |> fst |> msg_from_info))

(* Collecting input files into one big string *)

let maybe_input_line stdin =
  try Some (input_line stdin) with End_of_file -> None

let input_lines ic fn =
  let rec input lines =
    match maybe_input_line ic with
    | Some line -> input (line :: lines)
    | None -> ("?" ^ fn) :: List.rev lines
  in
  input []

let read (s : string) = input_lines (open_in s) s

let file_collection (def_files : string list) (protocol_file : string) : string
    =
  let lines = List.concat_map read (def_files @ [ protocol_file ]) in
  String.concat "\n" lines

let string_to_file s f =
  let out = open_out f in
  output_string out s;
  flush out;
  close out

(* Building expressions *)

(* Convert list of definitions and pre_expression to expression *)
let pre_to_e d_l pre_exp =
  let open Types in
  let d_l = List.rev d_l in
  let _ = typ_of_pre_exp d_l [] pre_exp in
  Ast.p_to_e [] d_l pre_exp []

(* Build expression from start to finish *)
let build_expression definition_files protocol_file =
  let s = file_collection definition_files protocol_file in
  match process s with
  | Ok (d_l, pre_exp) -> pre_to_e d_l pre_exp
  | Error msg -> failwith msg

(* Evaluate an expression given a list of valuations *)
let evaluate exp = Eval.eval [] exp
