%{
open Ast


  let (<+>) i1 i2 = {
    filename = if i1.filename = "" then i2.filename else i1.filename;
    start_lin = i1.start_lin;
    end_lin = i2.end_lin;
    start_col = i1.start_col;
    end_col = i2.end_col; 
  }
%}

(*%token <float Ast.info> FLT*)
%token <int Ast.info> INT
%token <string Ast.info> ID
%token <Ast.pre_info> TRUE 
%token <Ast.pre_info> FALSE 

%token <Ast.pre_info> TIMES
%token <Ast.pre_info> DIVIDES
%token <Ast.pre_info> PLUS
%token <Ast.pre_info> MINUS
%token <Ast.pre_info> GEQ
%token <Ast.pre_info> LEQ
%token <Ast.pre_info> EQUALS
%token <Ast.pre_info> AND
%token <Ast.pre_info> OR
%token <Ast.pre_info> NOT
%token <Ast.pre_info> LPAREN
%token <Ast.pre_info> RPAREN
%token <Ast.pre_info> COMMA
%token <Ast.pre_info> PERIOD
%token <Ast.pre_info> LET
%token <Ast.pre_info> IN
%token <Ast.pre_info> IF
%token <Ast.pre_info> THEN
%token <Ast.pre_info> ELSE
%token <Ast.pre_info> EVAL
%token <Ast.pre_info> MARK
%token <Ast.pre_info> MARKW
%token <Ast.pre_info> PIECE
%token <Ast.pre_info> SQUEEZE
%token <Ast.pre_info> INITIALIZE
%token <Ast.pre_info> DIVIDE
%token <Ast.pre_info> EOF
%token <Ast.pre_info> UNION
%token <Ast.pre_info> READ
%token <Ast.pre_info> DEF

%nonassoc IN ELSE
%left GEQ
%left TIMES
%left DIVIDES
%left PLUS
%left MINUS

%start <Ast.definition list * Ast.pre_expression> prog

%%


prog:
    | d_l = defn*; e = pre_exp; EOF { (d_l, e) }
    ;

pat:
    | x = ID { Var (snd x) }
    | LPAREN; pl = separated_list(COMMA, pat); RPAREN { List pl }
    ;

defn:
    | DEF; x = ID; idl = ID*; EQUALS; e = pre_exp {  {name = (snd x);  args = (snd (List.split(idl))); body = e} }

pre_exp:
    | n = INT; DIVIDES; d = INT; {  (fst n) <+> (fst d), Val (Real (snd n, Some (snd d))) } 
    | n = INT; PERIOD;  { (fst n), Val (Real (snd n, None)) }
    | n = INT           { (fst n), Val (Num (snd n)) } 
    | t = TRUE { (t, Val (Bool true))} 
    | f = FALSE {  (f, Val (Bool false)) } 
    | e1 = pre_exp; o = DIVIDES; n = INT { (o, Op (A Times, [(fst n, Val (Real (1, Some (snd n)))); e1]))  }
    | LPAREN; e = pre_exp; RPAREN { e } 
    | e1 = pre_exp; o = GEQ; e2 = pre_exp       { (o, Op (C Geq, [e1; e2])) } 
    | e1 = pre_exp; o = LEQ; e2 = pre_exp       { (o, Op (C Geq, [e2; e1])) } 
    | e1 = pre_exp; o = TIMES; e2 = pre_exp     { (o, Op (A Times, [e1; e2])) } 
    (*| e1 = pre_exp; o = DIVIDES; e2 = pre_exp { (o, Aop (Div, e1, e2)) }*)
    | e1 = pre_exp; o = PLUS; e2 = pre_exp      { (o, Op (A Plus, [e1; e2])) }
    | e1 = pre_exp; o = MINUS; e2 = pre_exp { let e' : pre_expression = (fst e2, Op (Neg, [e2])) in (o, Op (A Plus, [e1; e'])) }
    (*| e1 = pre_exp; o = MINUS; e2 = pre_exp { (o, Aop (Minus, e1, e2)) }*)
    | e1 = pre_exp; o = AND; e2 = pre_exp       { (o, Op (B And, [e1; e2])) }
    | e1 = pre_exp; o = OR; e2 = pre_exp        { (o, Op (B Or, [e1; e2])) } 
    | e1 = pre_exp; o = EQUALS; e2 = pre_exp    { (o, Op (C Eq, [e1; e2])) } 
    | n = NOT; e = pre_exp;                     { n, Op (Not, [e]) } 
    | x = ID ; LPAREN; args = separated_list(COMMA, pre_exp); r = RPAREN { ((fst x) <+> r, Abbreviation  (snd x, args)) }
    | PIECE; l = LPAREN; el = separated_list(COMMA, pre_exp); r = RPAREN; { (l <+> r, Piece el) }
    | i = PIECE; e = pre_exp { (i, Piece [e]) }
    | l = LPAREN; el = separated_list(COMMA, pre_exp); r = RPAREN; { (l <+> r, Tuple el) } 
    | i = IF; e1 = pre_exp; THEN; e2 = pre_exp; ELSE; e3 = pre_exp; { ( i <+> (fst e3), IfThenElse (e1, e2, e3)) } 
    | DIVIDE; l = LPAREN; e1 = pre_exp; COMMA; e2 = pre_exp; r = RPAREN; { l <+> r, Divide (e1, e2) } 
    | SQUEEZE; l = LPAREN; e = pre_exp; r = RPAREN; { l <+> r, Squeeze e}
    | i = INITIALIZE; { (i, Cake) } 
    | EVAL;l = LPAREN; e1 = pre_exp; COMMA; e2 = pre_exp; r = RPAREN; { l <+> r, Eval (e1, e2) } 
    | MARK; l = LPAREN; e1 = pre_exp ; COMMA; e2 = pre_exp; COMMA; e3 = pre_exp; r = RPAREN; { l <+> r, Mark (e1, e2, e3) }
    | MARKW; l = LPAREN; e1 = pre_exp ; COMMA; e2 = pre_exp; COMMA; e3 = pre_exp; r = RPAREN; { l <+> r, MarkW (e1, e2, e3) }  
    | LET; lp = LPAREN; l = separated_list(COMMA, pat); rp = RPAREN; EQUALS; e1 = pre_exp; IN; e2 = pre_exp; { lp <+> rp, Let (l, e1, e2) }
    | LET; x = ID ; EQUALS; e1 = pre_exp; IN; e2 = pre_exp { (fst x) <+> (fst e2), Let ([Var (snd x)], e1, e2) }
    | UNION; l = LPAREN; e1 = pre_exp; COMMA; e2 = pre_exp; r = RPAREN; { l <+> r, Union (e1, e2) }  
    | READ; x = ID { (fst x), Var (Read (snd x)) }
    | x = ID { (fst x), Var (N (snd x)) } 
