type variable = N of int list | Read of int list
type binding_variable = int list

val var_id : variable -> int list
val is_read : variable -> bool

type expression =
  | Val of Basic.value
  | Op of Basic.op * expression list
  | Var of variable
  | Let of binding_variable list * expression * expression
  | IfThenElse of expression * expression * expression
  | Tuple of expression list
  | Cake
  | Divide of expression * expression
  | Mark of expression * expression * expression
  | MarkW of expression * expression * expression
  | Eval of expression * expression
  | Piece of expression list
  | Squeeze of expression
  | Union of expression * expression

type pattern = Var of string | List of pattern list

val pattern_contains : string -> pattern -> bool

type pre_info = {
  filename : string;
  start_lin : int;
  end_lin : int;
  start_col : int;
  end_col : int;
}

type 'a info = pre_info * 'a

val msg_from_info : pre_info -> string

type pre_var = N of string | Read of string

val pre_var_id : pre_var -> string
val is_read_pre : pre_var -> bool

type pre_expression_no_info =
  | Val of Basic.value
  | Var of pre_var
  | Op of Basic.op * pre_expression list
  | Abbreviation of string * pre_expression list
  | Divide of pre_expression * pre_expression
  | Let of pattern list * pre_expression * pre_expression
  | IfThenElse of pre_expression * pre_expression * pre_expression
  | Tuple of pre_expression list
  | Mark of pre_expression * pre_expression * pre_expression
  | MarkW of pre_expression * pre_expression * pre_expression
  | Eval of pre_expression * pre_expression
  | Piece of pre_expression list
  | Squeeze of pre_expression
  | Cake
  | Union of pre_expression * pre_expression

(*re-define so info is outside of def, not inside*)
and pre_expression = pre_expression_no_info info

type definition = { name : string; args : string list; body : pre_expression }

val get_defn :
  definition list -> string -> pre_info -> definition * definition list

val p_to_e :
  int list ->
  definition list ->
  pre_expression ->
  (string * int list) list ->
  expression

val e_to_str : expression -> string
val def_to_str : definition -> string
val pat_to_str : pattern -> string
val var_string : int list -> string

val var_formatter : Format.formatter -> int list -> unit
[@@ocaml.toplevel_printer]

val var_list_formatter : Format.formatter -> int list list -> unit
[@@ocaml.toplevel_printer]

val e_formatter : Format.formatter -> expression -> unit
[@@ocaml.toplevel_printer]
