open Z3
open Z3.Symbol
open Z3.Arithmetic
open Z3.FuncDecl
open Formula
open Expression_to_formula
open Piece

(* This file converts formulas to smtlib instances using Z3's OCaml bindings *)
let p = Printf.sprintf
let map = List.map
let length = List.length
let ctx = mk_context [ ("unsat_core", "true") ]

(* Sorts required, besides tuple sorts, which are given below*)
let boolean = Boolean.mk_sort ctx
let num = Integer.mk_sort ctx
let real = Real.mk_sort ctx

let interval =
  Tuple.mk_sort ctx (mk_string ctx "interval")
    [ mk_string ctx "leftend"; mk_string ctx "rightend" ]
    [ real; real ]

let set = Set.mk_sort ctx interval
let str_to_sym s = mk_string ctx s
let concatu s1 s2 = s1 ^ "_" ^ s2

let rec sort_to_str (s : sort) =
  match s with
  | Num -> "num"
  | Real -> "real"
  | Val -> "Val"
  | Bool -> "bool"
  | Interval -> "interval"
  | Piece -> failwith "Unfinished"
  | Point -> "point"
  | Tup t_list -> List.fold_left concatu "tup" (List.map sort_to_str t_list)

let sort_to_symb t = str_to_sym (sort_to_str t)

let rec num_list n =
  if n > 0 then num_list (n - 1) @ [ str_to_sym (string_of_int n) ] else []

let rec sort_to_z3sort (s : sort) =
  match s with
  | Num -> num
  | Real -> real
  | Val -> real
  | Point -> real
  | Bool -> boolean
  | Interval -> interval
  | Piece -> failwith "Unfinished"
  | Tup t_list ->
      Tuple.mk_sort ctx (sort_to_symb s)
        (num_list (List.length t_list))
        (List.map sort_to_z3sort t_list)

let basic_pt_t_to_str pt_t =
  match pt_t with
  | M (_, m) -> mark_to_str m
  | P (i, (_, m)) -> p "lp_%i(%s)" i (mark_to_str m)

(* Makes the connection that the end points for a squeezed piece are the end points of the squeezed piece *)
let rec mark_reduce (pt : point) =
  match pt.lvl with
  | Cake -> pt.pt
  | Sq pc -> (
      match pt.pt with
      | L -> mark_reduce { lvl = pc.lvl; pt = fst (piece_endpoints pc.lst) }
      | R -> mark_reduce { lvl = pc.lvl; pt = snd (piece_endpoints pc.lst) }
      | _ -> pt.pt)

let lp_to_smt lp =
  let str =
    match snd lp with
    | L -> p "lp_%iSHOULDNOTEXIST" (fst lp)
    | R -> p "lp_%i(1)" (fst lp)
    | U i -> p "lp_%i(M%i)" (fst lp) i
  in
  Real.mk_const_s ctx str

let mark_to_smt m =
  match m with
  | L -> Real.mk_numeral_i ctx 0
  | R -> Real.mk_numeral_i ctx 1
  | U i -> Real.mk_const_s ctx (p "M%i" i)

let pt_to_smt pt_t =
  let mk_pt mt = mark_reduce { lvl = pc_t_to_lvl (fst mt); pt = snd mt } in
  match pt_t with
  | M mt -> mark_to_smt (mk_pt mt)
  | P (i, mt) -> lp_to_smt (i, mk_pt mt)

let interval =
  Tuple.mk_sort ctx (mk_string ctx "interval")
    [ mk_string ctx "leftend"; mk_string ctx "rightend" ]
    [ real; real ]

let v1 = mk_func_decl_s ctx "val1" [ interval ] real
let v2 = mk_func_decl_s ctx "val2" [ interval ] real
let v3 = mk_func_decl_s ctx "val3" [ interval ] real
let l = List.nth (Tuple.get_field_decls interval) 0
let r = List.nth (Tuple.get_field_decls interval) 1

let v_n (n : int) =
  match n with
  | 1 -> v1
  | 2 -> v2
  | 3 -> v3
  | _ -> failwith "Not currently a valuation defined here"

let rec int_list_to_var_name l =
  match l with
  | i :: l' -> string_of_int i ^ ":" ^ int_list_to_var_name l'
  | [] -> ""

let var_const (l, s) =
  Expr.mk_const_s ctx (int_list_to_var_name l) (sort_to_z3sort s)

let rec term_to_smt (t : term) =
  match t with
  | Pt pt_t -> pt_to_smt pt_t
  | Minus (t1, t2) -> minus_to_smt t1 t2
  | Op (A aop, [ t1; t2 ]) -> aop_to_smt aop t1 t2
  | Val (Real (n, d)) -> (
      match d with
      | Some d -> Real.mk_numeral_nd ctx n d
      | None -> Real.mk_numeral_i ctx n)
  (* Extra ops for more general translation *)
  | V (n, t) -> Expr.mk_app ctx (v_n n) [ term_to_smt t ]
  | Proj (n, t) ->
      Expr.mk_app ctx
        (List.nth (Tuple.get_field_decls (sort_to_z3sort (sort_of_term t))) n)
        [ term_to_smt t ]
  | LeftEnd t -> Expr.mk_app ctx l [ term_to_smt t ]
  | RightEnd t -> Expr.mk_app ctx r [ term_to_smt t ]
  | Interval (t1, t2) ->
      Expr.mk_app ctx
        (Tuple.get_mk_decl interval)
        [ term_to_smt t1; term_to_smt t2 ]
  | Tup t_list ->
      Expr.mk_app ctx
        (Tuple.get_mk_decl (sort_to_z3sort (sort_of_term t)))
        (List.map term_to_smt t_list)
  | Var (l, s) -> var_const (l, s)
  (* todo : | Op of op * term list *)
  (*and mark_term = piece_term * mark
    and point_term =
        | M of mark_term
        | P of int * mark_term
    and piece_term =
        | Cake
        | Sq of term
  *)
  | _ -> failwith "Not a real!"

and minus_to_smt t1 t2 = mk_sub ctx [ term_to_smt t1; term_to_smt t2 ]

and aop_to_smt aop t1 t2 =
  match aop with
  | Plus -> mk_add ctx [ term_to_smt t1; term_to_smt t2 ]
  | Times -> mk_mul ctx [ term_to_smt t1; term_to_smt t2 ]

let rec f_to_smt (f : formula) =
  match f with
  | True -> Boolean.mk_true ctx
  | False -> Boolean.mk_false ctx
  | Pred pred -> pred_to_smt pred
  | Neg f -> Boolean.mk_not ctx (f_to_smt f)
  | Implies (f1, f2) -> Boolean.mk_implies ctx (f_to_smt f1) (f_to_smt f2)
  | And f_list -> Boolean.mk_and ctx (map f_to_smt f_list)
  | Or f_list -> Boolean.mk_or ctx (map f_to_smt f_list)
  | ForAll (var_list, f) ->
      Quantifier.mk_forall_const ctx
        (List.map var_const var_list)
        (f_to_smt f) None [] [] None None
      |> Quantifier.expr_of_quantifier
  | Exists (var_list, f) ->
      Quantifier.mk_exists_const ctx
        (List.map var_const var_list)
        (f_to_smt f) None [] [] None None
      |> Quantifier.expr_of_quantifier
  | _ -> failwith "not allowed here"

and pred_to_smt (pred : predicate) =
  let cop, t1, t2 = pred in
  match cop with
  | Eq -> Boolean.mk_eq ctx (term_to_smt t1) (term_to_smt t2)
  | Geq -> mk_ge ctx (term_to_smt t1) (term_to_smt t2)

let and_to_sep f =
  match f with
  | And f_list -> map f_to_smt f_list
  | _ -> failwith "Not supposed to happen"
