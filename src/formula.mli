type sort =
  | Bool
  | Num
  | Real
  | Val
  | Point
  | Interval
  | Piece
  | Tup of sort list

type term =
  | Val of Basic.value
  | Pt of point_term
  | V of int * term
  | Op of Basic.op * term list
  | Minus of term * term
  | Var of int list * sort
  | Proj of int * term
  | LeftEnd of term
  | RightEnd of term
  | Interval of term * term
  | Piece of term list
  | Tup of term list

and mark_term = piece_term * Piece.mark
and point_term = M of mark_term | P of int * mark_term
and piece_term = Cake | Sq of term

type predicate = Basic.cop * term * term

type formula =
  | True
  | False
  | Sub of term
  | Pred of predicate
  | Neg of formula
  | And of formula list
  | Or of formula list
  | Implies of formula * formula
  | ForAll of (int list * sort) list * formula
  | Exists of (int list * sort) list * formula

val f_term : (term -> 'a) -> term -> term
val f_formula : 'a -> (term -> term) -> formula -> formula
val sort_of_term : term -> sort
val sort_to_str : sort -> string
val bool_to_formula : term -> formula
val subs_term : int list -> term -> term -> term
val sub_formula : int list -> term -> formula -> formula
val new_and : formula list -> formula
val new_or : formula list -> formula
val max_depth_term : term -> int
val term_to_str : term -> string
val pc_t_to_str : piece_term -> string
val mt_to_str : mark_term -> string
val pt_t_to_str : point_term -> string
val pred_to_str : predicate -> string
val term_formatter : Format.formatter -> term -> unit [@@ocaml.toplevel_printer]

val pc_t_formatter : Format.formatter -> piece_term -> unit
[@@ocaml.toplevel_printer]

val mt_formatter : Format.formatter -> mark_term -> unit
[@@ocaml.toplevel_printer]

val pt_t_formatter : Format.formatter -> point_term -> unit
[@@ocaml.toplevel_printer]

val pred_formatter : Format.formatter -> predicate -> unit
[@@ocaml.toplevel_printer]

val formula_formatter : Format.formatter -> formula -> unit
[@@ocaml.toplevel_printer]

val print_formula : formula -> unit
