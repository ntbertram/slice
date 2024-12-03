open Basic
(* This file is for generating example piecewise uniform valuations for evaluating protocols *)

let real_minus (r1 : real) (r2 : real) : real =
  let n, d = r2 in
  aop_real Plus r1 (-n, d)

let cmp_left_endpoint i1 i2 =
  if real_eq i1.l i2.l then 0 else if real_leq i1.l i2.l then -1 else 1


let has_overlap (i1 : interval) (i2 : interval) : bool =
  (real_leq i1.l i2.l && real_leq i2.l i1.r)
  || (real_leq i1.l i2.r && real_leq i2.r i1.r)
  || (real_leq i2.l i1.l && real_leq i1.l i2.r)
  || (real_leq i2.l i1.r && real_leq i1.r i2.r)

let real_min a b = if real_leq a b then a else b
let real_max a b = if real_geq a b then a else b
(* Assumes i1 and i2 overlap *)
let combine i1 i2 = { l = real_min i1.l i2.l; r = real_max i1.r i2.r }

let i_length (i : interval) : real = real_minus i.r i.l

(* Piecewise uniform preferences representation. Unrefined means that intervals are unsorted and could overlap. Refined means that intervals are sorted and cannot overlap *)
type pu_rep = 
    | Unrefined of interval list
    | Refined of interval list

let refine (p : pu_rep) : pu_rep = 
    match p with
    | Refined _ -> p
    | Unrefined i_list -> 
            (* Need to sort by left endpoint *)
            let i_list = List.sort cmp_left_endpoint i_list in
            let rec merge i i_list =
                match i_list with
                | i' :: i_list' -> 
                        if has_overlap i i' then
                            merge (combine i i') (i_list')
                        else 
                            (i, i_list)
                | [] -> (i, [])
            in
            let rec h i_list = 
                match i_list with
                | i :: i_list' -> 
                        let i, i_list' = merge i i_list' in
                        i :: (h i_list')
                | [] -> []
            in
            Refined (h i_list)

(** [pu_i_intersection rep_i] returns the intersection of i with rep 
    Examples: 
      [let i_list = \[\[1/8, 2/8\]; \[3/8, 4/8\]; \[6/8, 7/8\]\]]
      [pu_i_intersection i_list \[1/8, 4/8\]] returns [[1/8, 2/8]; [3/8, 4/8]]
      [pu_i_intersection i_list \[5/8, 11/16\]] returns []
      [pu_i_intersection i_list \[0, 1\]] returns i_list
      *)
let pu_i_intersection (rep : pu_rep) (i : interval) = 
    let rep = 
        match refine rep with
        | Refined rep -> rep
        | Unrefined _ -> failwith "Impossible"
    in
    rep
    |> List.map (fun rep_i -> {l = real_max rep_i.l i.l; r = real_min rep_i.r i.r})
    |> List.filter (fun rep_i -> (real_leq rep_i.l rep_i.r) && (not (real_geq rep_i.l rep_i.r))) 

(* Gives the length of the PU segment *)
let pu_rep_length (rep : pu_rep) =
    let rep = 
        match refine rep with
        | Refined rep -> rep
        | Unrefined _ -> failwith "Impossible"
    in
    rep |> List.fold_left (fun acc i -> (aop_real Plus acc (i_length i))) ((0, None)) 

(* Implements the eval for piecewise uniform valuations *)
let pu_eval (rep : pu_rep) (i : interval) =
    pu_rep_length (Refined (pu_i_intersection rep i))

(* Implements the mark for piecewise uniform valuations *)
let pu_mark (rep : pu_rep) (i : interval) (v : real) : real =
    let red_i_list = pu_i_intersection rep i in
    let rec h i_list v = 
        match i_list with
        | i_rep :: i_list' -> 
            if real_leq v (i_length i_rep) then
                aop_real Plus i_rep.l v
            else 
                h i_list' (real_minus v (i_length i_rep))
        | [] -> 
                if real_eq v (pu_eval rep i) && real_eq v (0, None) then
                    i.l
                else
                    let vi = pu_eval rep i in 
                    failwith (Printf.sprintf "Value supplied to mark (%s) is larger than value of supplied interval (%s)" (real_to_str v) (real_to_str vi))
    in
    let res = h red_i_list v in
    assert (real_eq (pu_eval rep {l = i.l; r = res}) v) ;
    res

let pu_valn (rep : pu_rep) : valn =
    let eval = pu_eval rep in
    let mark = pu_mark rep in
    {eval = eval; mark = mark}



(* Example interval lists and intervals  *)
let i_list : interval list =
  [
    { l = (3, Some 8); r = (4, Some 8) };
    { l = (1, Some 8); r = (2, Some 8) };
    { l = (6, Some 8); r = (7, Some 8) };
  ]

let cake = { l = (0, None); r = (1, None) } 
let i1 = { l = (1, Some 8); r = (4, Some 8) } (* 2/8 good *)
let i2 = { l = (5, Some 16); r = (13, Some 16) } (* 3/16 good *)
let i3 = { l = (3, Some 16); r = (7, Some 16) } (* 1/8 good *)
let i4 = { l = (5, Some 8); r = (11, Some 16) } (* 0 good *)
let i5 = { l = (0, None); r = (1, None) } (* 3/8 good *)




let pu_rep_examples = 
    [Unrefined [i1; i2]; Unrefined [i3; i4]; Unrefined [i2; i3; i4]; Unrefined [i5]]

let default_valuations = 
    List.map pu_valn pu_rep_examples

let uniform_valuations =
    List.map pu_valn (List.init 4 (fun _ -> Refined [cake]))


(** [interval_mark i_list start value] returns the leftmost mark to the right of 
    [start], let us call it m, for which the interval \[[start], m\] has the length of
    [value]. [i_list] is the list of piecewise uniform intervals.
    
    Requires: [i_list] is mutually disjoint
    
    Examples: 
      [let i_list = \[\[1/8, 2/8\]; \[3/8, 4/8\]; \[6/8, 7/8\]\]]
      [interval_mark i_list 0 [1/8]] returns [1/4]
      [interval_mark i_list 0 [2/8]] returns [1/2]
      [interval_mark i_list 0 [3/8]] returns [7/8]
      [interval_mark i_list 0 [3/16]] returns [7/16]
      [interval_mark i_list [5/16] [1/8]] returns [1/2]
       *)

type t = M of int * int | P of int * int * int

let locations =
  [
    (P (1, 1, 1), (0, None));
    (P (2, 1, 1), (0, None));
    (P (2, 0, 0), (1, None));
    (P (1, 0, 0), (3, Some 4));
    (M (1, 1), (1, Some 4));
    (M (0, 0), (1, None));
  ]

let print_intervals i_list =
  List.map
    (fun x ->
      print_endline ("[" ^ real_to_str x.l ^ ", " ^ real_to_str x.r ^ "]"))
    i_list
