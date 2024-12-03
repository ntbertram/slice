type mark = 
    | L
    | R
    | U of int
type lp = int * mark
type interval = { l : mark; r : mark }
type level = 
    | Cake
    | Sq of piece
and piece = {lvl : level; lst : interval list}
type point = {lvl : level; pt : mark}
type vinterval = {lvl : level; i : interval}

val form_interval : point -> point -> vinterval
val form_piece : vinterval list -> piece

type mark_order = mark list

val suffix : 'a -> 'a list -> 'a list
val prefix : 'a -> 'a list -> 'a list

val sort_piece : mark_order -> interval list -> interval list
val contained_in : mark_order -> interval -> interval -> bool

val tot_piece : interval list

val relax_interval : mark_order -> vinterval -> piece
val piece_endpoints : interval list -> mark * mark

val all_possible_insertions : mark_order -> interval list -> mark_order -> mark_order list

val mark_to_str: mark -> string

val mark_formatter : Format.formatter -> mark -> unit [@@ocaml.toplevel_printer]
val interval_formatter : Format.formatter -> interval -> unit [@@ocaml.toplevel_printer]
val piece_formatter : Format.formatter -> piece -> unit [@@ocaml.toplevel_printer]
val lvl_formatter : Format.formatter -> level -> unit [@@ocaml.toplevel_printer]
val mark_order_formatter : Format.formatter -> mark_order -> unit [@@ocaml.toplevel_printer]
