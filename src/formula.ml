open Basic
open Types
open List
open Piece

let p = Printf.sprintf
(*let concatcom s1 s2 = s1 ^ ", " ^ s2*)

type sort =
  | Bool
  | Num
  | Real
  | Val
  | Point
  | Interval
  | Piece
  | Tup of sort list

let rec typ_to_sort (typ : typ) : sort =
  match typ with
  | Un Bool -> Bool
  | Un Num -> Num
  | Un Real -> Real
  | Un Val -> Val
  | Un Point -> Point
  | Un RInterval -> Interval
  | Un RPiece -> Piece
  | Lin Interval -> Interval
  | Lin Piece -> Piece
  | Lin (Tup t_list) -> Tup (List.map typ_to_sort t_list)

let sort_to_utyp s : utyp =
  match s with
  | Bool -> Bool
  | Num -> Num
  | Real -> Real
  | Val -> Val
  | Point -> Point
  | Interval -> RInterval
  | Piece -> RPiece
  | _ -> failwith "Cannot convert tup sort to utyp"

let sort_of_val v = typ_to_sort (type_of_value v)

let rec sort_to_str s =
  match s with
  | Interval -> "Interval"
  | Piece -> "Piece"
  | Tup t_list -> (
      match List.map sort_to_str t_list with
      | h :: t -> List.fold_left concatspec h t
      | [] -> failwith "sort of empty tup")
  | Bool -> "Bool"
  | Num -> "Num"
  | Real -> "Real"
  | Point -> "Point"
  | Val -> "Val"

type term =
  | Val of value
  | Pt of point_term
  | V of int * term
  | Op of op * term list
  | Minus of term * term
  | Var of int list * sort
  | Proj of int * term
  | LeftEnd of term
  | RightEnd of term
  | Interval of term * term
  | Piece of term list
  | Tup of term list

and mark_term = piece_term * mark
and point_term = M of mark_term | P of int * mark_term
and piece_term = Cake | Sq of term

type predicate = cop * term * term

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

let rec f_term f (t : term) : term =
  match t with
  | Val _ -> t
  | Op (op, t_list) -> Op (op, List.map (f_term f) t_list)
  | Pt pt_t -> Pt (f_term_pt f pt_t)
  | V (n, t) -> V (n, f_term f t)
  | Minus (t1, t2) -> Minus (f_term f t1, f_term f t2)
  | Var (l, typ) -> Var (l, typ)
  | Proj (n, v) -> Proj (n, f_term f v)
  | LeftEnd v -> LeftEnd (f_term f v)
  | RightEnd v -> RightEnd (f_term f v)
  | Interval (t1, t2) -> Interval (f_term f t1, f_term f t2)
  | Tup t_list -> Tup (map (f_term f) t_list)
  | Piece t_list -> Piece (map (f_term f) t_list)

and f_term_mark f (pc_t, m) = (f_term_pc f pc_t, m)

and f_term_pt f pt_t =
  match pt_t with
  | M mt -> M (f_term_mark f mt)
  | P (i, mt) -> P (i, f_term_mark f mt)

and f_term_pc f pc_t = match pc_t with Cake -> Cake | Sq t -> Sq (f_term f t)

let rec f_formula f fv (foe : formula) =
  match foe with
  | True -> True
  | False -> False
  | Sub t -> Sub (fv t)
  | Pred (cop, t1, t2) -> Pred (cop, fv t1, fv t2)
  | Implies (foe1, foe2) -> Implies (f_formula f fv foe1, f_formula f fv foe2)
  | And foe_list -> And (map (f_formula f fv) foe_list)
  | Or foe_list -> Or (map (f_formula f fv) foe_list)
  | Neg foe -> Neg (f_formula f fv foe)
  | ForAll (t_list, foe) -> ForAll (t_list, f_formula f fv foe)
  | Exists (t_list, foe) -> ForAll (t_list, f_formula f fv foe)

let rec sort_of_term (t : term) : sort =
  match t with
  | Val v -> sort_of_val v
  | V _ -> Val
  | Op (op, t_list) ->
      let ut_list =
        List.map (fun t -> t |> sort_of_term |> sort_to_utyp) t_list
      in
      typ_to_sort (Un (sgn op ut_list).ret)
  | Pt pt_t -> (
      match pt_t with
      | M (pc_t, _) ->
          piece_term_type pc_t;
          Real
      | P (_, (pc_t, _)) ->
          piece_term_type pc_t;
          Real)
  | Minus (t1, t2) -> (
      match (sort_of_term t1, sort_of_term t2) with
      | Real, Real -> Real
      | Num, Num -> Num
      | _ -> failwith "Not correct use of minus")
  | Var (_, s) -> s
  | Proj (n, t) -> (
      let s = sort_of_term t in
      match s with
      | Tup s_list -> nth s_list n
      | _ -> failwith "Expected tuple, did not receive a tuple")
  | LeftEnd t ->
      let s = sort_of_term t in
      if s = Interval then Real
      else
        failwith (p "LeftEnd expexcted Interval. Received %s" (sort_to_str s))
  | RightEnd t ->
      let s = sort_of_term t in
      if s = Interval then Real
      else
        failwith (p "LeftEnd expexcted Interval. Received %s" (sort_to_str s))
  | Interval (t1, t2) -> (
      match (sort_of_term t1, sort_of_term t2) with
      | Real, Real -> Interval
      | s1, s2 ->
          failwith
            (p "Interval constructor expected Reals. Received %s, and %s."
               (sort_to_str s1) (sort_to_str s2)))
  | Tup t_list -> Tup (List.map sort_of_term t_list)
  | Piece t_list -> sort_piece t_list

and sort_piece t_list =
  let s_list = List.map sort_of_term t_list in
  let wrong =
    filter_map (fun (s : sort) -> if s = Interval then None else Some s) s_list
  in
  match wrong with
  | [] -> Piece
  | _ -> failwith "Tried to construct a piece using non-intervals!"

and piece_term_type pc_t =
  match pc_t with
  | Cake -> ()
  | Sq t ->
      let s = sort_of_term t in
      if s = Piece then ()
      else
        failwith
          (p "Expected piece for interval level. Received %s" (sort_to_str s))

let new_and term_list =
  let surface_term t =
    match t with And t_list -> t_list | True -> [] | _ -> [ t ]
  in
  And (fold_left (fun l t -> l @ surface_term t) [] term_list)

let new_or term_list =
  let surface_term t = match t with Or t_list -> t_list | _ -> [ t ] in
  Or (fold_left (fun l t -> l @ surface_term t) [] term_list)

(* Substitution *)

let rec subs_term l t_new t =
  match t with
  | Var (l', _) -> if l = l' then t_new else t
  | Val v -> Val v
  | Op (op, t_list) -> Op (op, List.map (subs_term l t_new) t_list)
  | Pt pt_t -> Pt (subs_pt_t l t_new pt_t)
  | LeftEnd v -> LeftEnd (subs_term l t_new v)
  | RightEnd v -> RightEnd (subs_term l t_new v)
  | V (n, t) -> V (n, subs_term l t_new t)
  | Proj (n, v) -> Proj (n, subs_term l t_new v)
  | Minus (t1, t2) -> Minus (subs_term l t_new t1, subs_term l t_new t2)
  | Interval (t1, t2) -> Interval (subs_term l t_new t1, subs_term l t_new t2)
  | Tup t_list -> Tup (List.map (subs_term l t_new) t_list)
  | Piece t_list -> Piece (List.map (subs_term l t_new) t_list)

and subs_pc_t l t_new pc_t =
  match pc_t with Cake -> Cake | Sq t -> Sq (subs_term l t_new t)

and subs_mt l t_new (pc_t, m) = (subs_pc_t l t_new pc_t, m)

and subs_pt_t l t_new pt_t =
  match pt_t with
  | M mt -> M (subs_mt l t_new mt)
  | P (i, mt) -> P (i, subs_mt l t_new mt)

let rec bool_to_formula (t : term) =
  match t with
  | Val (Bool true) -> True
  | Val (Bool false) -> False
  | Op (B And, [ t1; t2 ]) -> new_and [ bool_to_formula t1; bool_to_formula t2 ]
  | Op (B Or, [ t1; t2 ]) -> new_or [ bool_to_formula t1; bool_to_formula t2 ]
  | Op (C cop, [ t1; t2 ]) -> Pred (cop, t1, t2)
  | Op (Not, [ t ]) -> Neg (bool_to_formula t)
  | Var (l, typ) -> Sub (Var (l, typ))
  | Proj (n, t) -> Sub (Proj (n, t))
  | _ -> failwith "Cannot convert term to boolean formula"

let rec sub_formula l t_new f =
  match f with
  | Sub t -> (
      match t with
      | Var (l', _) -> if l = l' then bool_to_formula t_new else f
      | _ -> Sub (subs_term l t_new t))
  | _ -> f_formula (sub_formula l t_new) (subs_term l t_new) f

let rec max_depth_term t =
  let f = max_depth_term in
  match t with
  | V (_, t) -> f t + 1
  | Minus (t1, t2) -> max (f t1) (f t2) + 1
  | Proj (_, t) -> f t + 1
  | LeftEnd t -> f t + 1
  | RightEnd t -> f t + 1
  | Interval (t1, t2) -> max (f t1) (f t2) + 1
  | Piece t_list -> List.fold_left (fun m t -> max m (f t)) 0 t_list + 1
  | Tup t_list -> List.fold_left (fun m t -> max m (f t)) 0 t_list + 1
  | Op (_, t_list) -> List.fold_left (fun m t -> max m (f t)) 0 t_list + 1
  | Pt pt_t -> md_pt_t pt_t
  | _ -> 0

and md_pt_t pt_t =
  match pt_t with M (pc_t, _) -> md pc_t | P (_, (pc_t, _)) -> md pc_t

and md pc_t = match pc_t with Cake -> 0 | Sq t -> max_depth_term t

let rec term_to_str (v : term) =
  match v with
  | Val v -> value_to_str v
  | Pt pt_t -> pt_t_to_str pt_t
  | V (n, t) -> p "V (%i, %s)" n (term_to_str t)
  | Minus (t1, t2) -> p "%s - %s" (term_to_str t1) (term_to_str t2)
  | Var _ -> p "Var"
  | Op (op, [ v1; v2 ]) ->
      p "%s %s %s" (term_to_str v1) (op_as_str op) (term_to_str v2)
  | Proj (n, v) -> p "#%i %s" n (term_to_str v)
  | LeftEnd v -> p "l(%s)" (term_to_str v)
  | RightEnd v -> p "r(%s)" (term_to_str v)
  | Interval (t1, t2) -> p "[%s, %s]" (term_to_str t1) (term_to_str t2)
  | Piece t_list -> p "pc %s" (t_list_to_str t_list)
  | Tup t_list -> p "(%s)" (t_list_to_str t_list)
  | Op (Not, [ t ]) -> p "¬%s" (term_to_str t)
  | Op (Neg, [ t ]) -> p "-%s" (term_to_str t)
  | Op (op, t_list) -> p "%s (%s)" (op_as_str op) (t_list_to_str t_list)

and t_list_to_str t_list =
  let help init t_list =
    fold_left (fun s t -> s ^ ", " ^ term_to_str t) init t_list
  in
  match t_list with h :: t -> help (term_to_str h) t | [] -> ""

and pc_t_to_str pc_t =
  match pc_t with Cake -> "" | Sq t -> p "%s" (term_to_str t)

and mt_to_str (pc_t, m) =
  let s1 = pc_t_to_str pc_t in
  if s1 = "" then p "%s" (mark_to_str m) else p "{%s} %s" s1 (mark_to_str m)

and pt_t_to_str pt_t =
  match pt_t with
  | M mt -> mt_to_str mt
  | P (i, mt) -> p "%s:%i" (mt_to_str mt) i

let pred_to_str pred =
  let cop, t1, t2 = pred in
  p "(%s %s %s)" (cop_to_str cop) (term_to_str t1) (term_to_str t2)

open Format

let kwd = pp_print_string
let num = pp_print_int
let spc = pp_print_space

let rec term_formatter fmt t =
  let tf = term_formatter in
  match t with
  | Val v -> value_formatter fmt v
  | Pt pt_t -> pt_t_formatter fmt pt_t
  | V (n, t) ->
      kwd fmt "V (";
      num fmt n;
      kwd fmt ",";
      pp_open_hovbox fmt 0;
      tf fmt t;
      close_box ();
      kwd fmt ")"
  | Minus (t1, t2) ->
      tf fmt t1;
      spc fmt ();
      kwd fmt "-";
      spc fmt ();
      tf fmt t2
  | Var (l, _) ->
      kwd fmt "Var";
      num fmt (List.hd l)
  | Proj (n, t) ->
      kwd fmt "#";
      num fmt n;
      tf fmt t
  | LeftEnd t ->
      kwd fmt "l ";
      tf fmt t
  | RightEnd t ->
      kwd fmt "r ";
      tf fmt t
  | Interval (t1, t2) ->
      kwd fmt "[";
      tf fmt t1;
      kwd fmt ", ";
      tf fmt t2;
      kwd fmt "]"
  | Piece t_list ->
      kwd fmt "pc ";
      pp_open_hovbox fmt 0;
      t_list_formatter fmt t_list;
      close_box ()
  | Tup t_list ->
      kwd fmt "(";
      pp_open_hovbox fmt 0;
      t_list_formatter fmt t_list;
      kwd fmt ")";
      close_box ()
  | Op (Not, [ t ]) ->
      kwd fmt "¬";
      tf fmt t
  | Op (Neg, [ t ]) ->
      kwd fmt "-";
      tf fmt t
  | Op (op, [ t1; t2 ]) ->
      open_hovbox 0;
      tf fmt t1;
      kwd fmt (op_as_str op);
      tf fmt t2;
      close_box ()
  | Op (op, l) ->
      open_hovbox 0;
      kwd fmt (op_as_str op);
      spc fmt ();
      kwd fmt "(";
      t_list_formatter fmt l;
      kwd fmt ")";
      close_box ()

and t_list_formatter fmt t_list =
  match t_list with
  | t :: [] -> term_formatter fmt t
  | t :: t_list' ->
      term_formatter fmt t;
      kwd fmt ", ";
      t_list_formatter fmt t_list'
  | [] -> ()

and pc_t_formatter fmt pc_t =
  match pc_t with
  | Cake -> ()
  | Sq t ->
      kwd fmt "{";
      term_formatter fmt t;
      kwd fmt "} "

and mt_formatter fmt (pc_t, m) =
  pc_t_formatter fmt pc_t;
  mark_formatter fmt m

and pt_t_formatter fmt pt_t =
  match pt_t with
  | M mt -> kwd fmt (mt_to_str mt)
  | P (i, mt) -> kwd fmt (p "%s:%i" (mt_to_str mt) i)

let pred_formatter fmt (cop, t1, t2) =
  term_formatter fmt t1;
  spc fmt ();
  kwd fmt (cop_to_str cop);
  spc fmt ();
  term_formatter fmt t2

let rec formula_formatter fmt (f : formula) =
  match f with
  | True -> kwd fmt "True"
  | False -> kwd fmt "False"
  | Pred pred ->
      pp_open_hovbox fmt 0;
      kwd fmt "(";
      pred_formatter fmt pred;
      kwd fmt ")";
      close_box ()
  | Implies (f1, f2) ->
      pp_open_hovbox fmt 0;
      kwd fmt "(";
      formula_formatter fmt f1;
      kwd fmt ")";
      pp_print_space fmt ();
      kwd fmt "=>";
      pp_print_break fmt 1 2;
      kwd fmt "(";
      formula_formatter fmt f2;
      kwd fmt ")";
      close_box ()
  | And f_list ->
      pp_open_hvbox fmt 2;
      pp_print_break fmt 0 0;
      kwd fmt "[";
      pp_print_break fmt 0 0;
      pp_open_box fmt 0;
      pp_print_break fmt 0 0;
      and_list fmt f_list;
      pp_print_break fmt 0 0;
      close_box ();
      pp_print_break fmt 0 0;
      kwd fmt "]";
      close_box ()
  | Or f_list ->
      pp_open_hvbox fmt 2;
      pp_print_break fmt 0 0;
      kwd fmt "[";
      pp_print_break fmt 0 0;
      pp_open_box fmt 0;
      pp_print_break fmt 0 0;
      or_list fmt f_list;
      pp_print_break fmt 0 0;
      close_box ();
      pp_print_break fmt 0 0;
      kwd fmt "]";
      close_box ()
  | Neg f ->
      kwd fmt "¬";
      kwd fmt "(";
      formula_formatter fmt f;
      kwd fmt ")"
  | ForAll (t_list, c) ->
      pp_open_hovbox fmt 0;
      kwd fmt "∀";
      kwd fmt (f_quant (length t_list) true);
      pp_print_break fmt 1 4;
      formula_formatter fmt c;
      close_box ()
  | Exists (t_list, c) ->
      pp_open_hovbox fmt 0;
      kwd fmt "∃";
      kwd fmt (f_quant (length t_list) true);
      pp_print_break fmt 1 4;
      formula_formatter fmt c;
      close_box ()
  | Sub _ -> failwith "Currently not supported"

and and_list fmt f_list =
  match f_list with
  | f :: [] -> formula_formatter fmt f
  | f :: t ->
      formula_formatter fmt f;
      pp_print_break fmt 1 0;
      kwd fmt "∧";
      pp_print_break fmt 1 0;
      and_list fmt t
  | [] -> ()

and or_list fmt f_list =
  match f_list with
  | f :: [] -> formula_formatter fmt f
  | f :: t ->
      formula_formatter fmt f;
      pp_print_break fmt 1 0;
      kwd fmt "v";
      pp_print_break fmt 1 0;
      or_list fmt t
  | [] -> ()

and f_quant n last =
  let str = if last then "." else ", " in
  match n with 0 -> "" | n -> p "%sret%i%s" (f_quant (n - 1) false) n str

let print_formula f = formula_formatter std_formatter f
