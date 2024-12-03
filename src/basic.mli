type aop =
    | Plus
    | Times

type cop =
    | Geq
    | Eq

type bop =
    | And
    | Or

type op =
    | A of aop
    | B of bop
    | C of cop
    | Not
    | Neg


type real = int * (int option)


val comp : cop -> 'a -> 'a -> bool
val cross_multiply : real -> real -> int * int
val reduce : real -> real
val real_eq : real -> real -> bool
val real_geq : real -> real -> bool
val real_leq : real -> real -> bool
val aop_num : aop -> int -> int -> int
val aop_real : aop -> real -> real -> real
val aop_real_list : aop -> real list -> real
val negate : real -> real
val minus : real -> real -> real


type interval = {l : real; r : real}

type piece = {lvl : level; pc : interval list}
and level =
    | Cake
    | Sq of piece

type vinterval = {lvl : level; i : interval}
type point = {lvl : level; pt : real}

val sort_pc : piece -> piece
val piece_length : piece -> real

type pt_containment =
    | Left
    | Right
    | Inside

val cont : real -> interval -> pt_containment
val intersect : interval -> interval list -> interval list
val contains : piece -> point -> bool
val squeeze_piece : piece -> vinterval

val unsqueeze_pt : point -> point
val unsqueeze_i : vinterval -> piece
val new_point : piece -> point -> point

val make_piece : vinterval list -> piece
val divide : vinterval -> point -> vinterval * vinterval

type valn = { eval : (interval -> real); mark : (interval -> real -> real)}
type agent_valns = valn list

type value =
    | Real of real
    | Num of int
    | Bool of bool
    | Tup of value list
    | Point of point
    | Interval of vinterval 
    | Piece of piece

val val_eq: value -> value -> bool
val apply_op: op -> value list -> value



val aop_to_str : aop -> string
val bop_to_str : bop -> string
val cop_to_str : cop -> string
val op_to_str : op -> string list -> string

val op_as_str : op -> string


val real_to_str : real -> string
val piece_to_str : piece -> string
val lvl_to_str : level -> string
val vinterval_to_str : vinterval -> string
val point_to_str : point -> string
val value_to_str : value -> string


val real_formatter : Format.formatter -> real -> unit [@@ocaml.toplevel_printer]
val interval_formatter : Format.formatter -> interval -> unit [@@ocaml.toplevel_printer]
val piece_formatter : Format.formatter -> piece -> unit [@@ocaml.toplevel_printer]
val lvl_formatter : Format.formatter -> level -> unit [@@ocaml.toplevel_printer]
val vinterval_formatter : Format.formatter -> vinterval -> unit [@@ocaml.toplevel_printer]
val point_formatter : Format.formatter -> point -> unit [@@ocaml.toplevel_printer]
val value_formatter : Format.formatter -> value -> unit [@@ocaml.toplevel_printer]
