{
open Parser
open Ast

  let info_of_buf lexbuf = 
    let open Lexing in 
    let start = lexbuf.lex_start_p in
    let curr = lexbuf.lex_curr_p in {
      filename = curr.pos_fname;
      start_lin = curr.pos_lnum;
      end_lin = curr.pos_lnum;
      start_col = start.pos_cnum - start.pos_bol + 1;
      end_col = curr.pos_cnum - start.pos_bol + 1;
    }



  exception LexingError of string info


}

let white = [' ' '\t']+
(*let comment = '(' '*' _* '*' ')'*)
let digit = ['0'-'9']
let int = '-'? digit+
(* let float = '-'? digit+'.'digit* *)
let letter = ['a'-'z' 'A'-'Z']
let letter_or_extra = letter | '_' | '\'' | digit
let id = letter+ letter_or_extra*
let newfile = '?' ['a'-'z' 'A'-'Z' '0'-'9' '.' '/' '-' '_']+

rule read = 
    parse
    | "\n" { Lexing.new_line lexbuf; read lexbuf }
    | white { read lexbuf }
    | "(*" {comment 0 lexbuf }
    | "true" { TRUE (info_of_buf lexbuf)}
    | "false" { FALSE (info_of_buf lexbuf)}
    | ">=" { GEQ (info_of_buf lexbuf)}
    | "<=" { LEQ (info_of_buf lexbuf)}
    | "*" { TIMES (info_of_buf lexbuf)}
    | "/" { DIVIDES (info_of_buf lexbuf)}
    | "+" { PLUS (info_of_buf lexbuf)}
    | "-" { MINUS (info_of_buf lexbuf)}
    | "&" { AND (info_of_buf lexbuf)}
    | "|" { OR (info_of_buf lexbuf)}
    | "not" { NOT (info_of_buf lexbuf)}
    | "=" { EQUALS (info_of_buf lexbuf)}
    | "(" { LPAREN (info_of_buf lexbuf)}
    | ")" { RPAREN (info_of_buf lexbuf)}
    | "," { COMMA (info_of_buf lexbuf)}
    | "." { PERIOD (info_of_buf lexbuf)}
    | "let" { LET (info_of_buf lexbuf)}
    | "in" { IN (info_of_buf lexbuf)}
    | "if" { IF (info_of_buf lexbuf)}
    | "then" { THEN (info_of_buf lexbuf)}
    | "else" { ELSE (info_of_buf lexbuf)}
    | "eval" { EVAL (info_of_buf lexbuf)}
    | "mark" { MARK (info_of_buf lexbuf)}
    | "markw" { MARKW (info_of_buf lexbuf)}
    | "divide" { DIVIDE (info_of_buf lexbuf)}
    | "initialize" { INITIALIZE (info_of_buf lexbuf)}
    | "cake" { INITIALIZE (info_of_buf lexbuf)}
    | "squeeze" { SQUEEZE (info_of_buf lexbuf)}
    | "piece" { PIECE (info_of_buf lexbuf) }
    | "union" { UNION (info_of_buf lexbuf)}
    | "read" { READ (info_of_buf lexbuf)}
    | "def" { DEF (info_of_buf lexbuf)}
    | newfile {lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_lnum = -1;
              Lexing.pos_fname = let fn = Lexing.lexeme lexbuf in String.sub fn 1 ((String.length fn) - 1)}; 
              Lexing.new_line lexbuf; read lexbuf}
    (*| float { FLT (info_of_buf lexbuf, float_of_string (Lexing.lexeme lexbuf)) }*)
    | int { INT (info_of_buf lexbuf, int_of_string (Lexing.lexeme lexbuf)) }
    | id { ID (info_of_buf lexbuf, Lexing.lexeme lexbuf) }
    | eof { EOF (info_of_buf lexbuf) }
    | _ as x      { raise (LexingError (info_of_buf lexbuf, "unexpected character " ^ String.make 1 x)) }
and comment depth =
    parse
    | "(*" { comment (depth + 1) lexbuf }
    | "*)" { if depth = 0 then read lexbuf else comment (depth - 1) lexbuf }
    | eof {EOF (info_of_buf lexbuf) }
    | _ { comment depth lexbuf }
