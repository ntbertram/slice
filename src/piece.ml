let p = Printf.sprintf

(* This file gives the formulaic version of pieces, built from intervals, which are built from marks *)

(*Here L is 0 and R is 1. U is an unknown variable representing a mark within the protocol. The int counts the current number of marks*)
type mark = L | R | U of int

(* lp is a left point of an agent that represents the left endpoint of a nonzero region for a given agent *)
type lp = int * mark

(*
    We assume that there is an ordered list of all the marks in a protocol.
     A piece is then a list of pairs of marks, where the first mark is <= the second mark.
     The piece need not be ordered.
*)
type interval = { l : mark; r : mark }

(* For the purposes of this artifact, the level of pieces, intervals, and points are not relevant and can be effectively ignored *)
type level = Cake | Sq of piece
and piece = { lvl : level; lst : interval list }

type point = { lvl : level; pt : mark }
type vinterval = { lvl : level; i : interval }

let form_interval (pt1 : point) (pt2 : point) =
  assert (pt1.lvl = pt2.lvl);
  let i = { l = pt1.pt; r = pt2.pt } in
  { lvl = pt1.lvl; i }

let form_piece (lst : vinterval list) : piece =
  let rec h lvl lst =
    match lst with
    | i :: lst' ->
        if lvl = i.lvl then i.i :: h lvl lst'
        else
          failwith
            "Cannot form piece as all intervals do not have the same structure!"
    | [] -> []
  in
  match lst with
  | i :: lst' -> { lvl = i.lvl; lst = i.i :: h i.lvl lst' }
  | [] -> failwith "Trying to make an empty piece!"

type mark_order = mark list

(* Assumes that both marks are contained in the ordering *)
let compare_m (o : mark_order) (m : mark) (m' : mark) =
  let rec helper o m m' =
    match o with
    | mo :: o' -> (
        match (mo = m, mo = m') with
        | true, true -> 0 (* m = m' *)
        | true, false -> -1 (* m < m' *)
        | false, true -> 1 (* m' < m *)
        | false, false -> helper o' m m' (* Not sure yet *))
    | [] -> failwith "Neither mark is found within the ordering"
  in
  helper o m m'

let leq_m o m m' = 
    match compare_m o m m' with
    | -1 -> true
    | 1 -> false
    | 0 -> true
    | _ -> failwith "Illegal comparison. Should never occur."

  (* Compares the left endpoints of intervals. If equal, compares right endpoints. *)
let compare_i o i i' = 
    let res = compare_m o i.l i'.l in
    if res = 0 then
        compare_m o i.r i'.r 
    else
        res

let new_sort_piece o p = List.stable_sort (compare_i o) p

let max_m o m m' = if leq_m o m m' then m' else m

(* This combines overlapping pieces for a "normal form" representation of a piece *)
let refine o p = 
    (* Need to sort by left endpoint *)
    let p = new_sort_piece o p in
    let rec merge i p =
        match p with
        | i' :: p' -> 
                (* i and i' overlap *)
                if leq_m o i'.l i.r then
                    merge {l = i.l; r = (max_m o i.r i'.r)} (p')
                else 
                    (i, p)
        | [] -> (i, [])
    in
    let rec h p = 
        match p with
        | i :: p' -> 
                let i, p' = merge i p' in
                i :: (h p')
        | [] -> []
    in
    h p


let atomic_interval_representation o i =
    let rec h o i = 
        match o with
        | m :: m' :: o' -> 
                begin
                match m = i.l, m' = i.r with
                | true, false ->
                    {l = m; r = m'} :: (h (m' :: o') {l = m'; r = i.r})
                | true, true -> [i]
                | false, false -> h (m' :: o') i
                | false, true -> failwith "Should not occur! Interval is imcompatible with mark ordering!"
                end
        | _ :: [] -> []
        | [] -> failwith "Mark order supplied is empty!"
    in h o i


    (* Assumes piece is refined *)
let atomic_piece_representation o p = List.fold_left (fun acc i -> acc @ (atomic_interval_representation o i)) [] p





let compare o i i' =
  match (leq_m o i.l i'.l, leq_m o i'.l i.l) with
  | true, true -> 0
  | true, false -> -1
  | false, true -> 1
  | _ -> failwith "cannot happen"

let sort_piece o p = List.stable_sort (compare o) p

(* Intervals are assumed to be well-formed *)
let contained_in (o : mark_order) (i : interval) (i' : interval) =
  let lte = leq_m o in
  lte i'.l i.l && lte i.r i'.r

let mark_inside (o : mark_order) (m : mark) (i : interval) =
  let lte = leq_m o in
  lte i.l m && lte m i.r

let tot_piece = [ { l = L; r = R } ]
let mark_to_str v = match v with L -> "L" | R -> "R" | U i -> p "M%i" i
let interval_to_str i = p "[%s, %s]" (mark_to_str i.l) (mark_to_str i.r)

let piece_to_str (pc : piece) =
  let rec helper lst =
    match lst with
    | i :: [] -> p "%s" (interval_to_str i)
    | i :: lst' -> p "%s, " (interval_to_str i) ^ helper lst'
    | [] -> ""
  in
  let pre =
    match pc.lvl with Cake -> "" | Sq pc -> p "{%s} " (helper pc.lst)
  in
  pre ^ helper pc.lst

let rec mark_order_to_str o =
  match o with
  | m :: [] -> mark_to_str m
  | m :: o' -> p "%s ≤ " (mark_to_str m) ^ mark_order_to_str o'
  | [] -> ""

(* Returns the interval within the piece that contains the mark *)
let mark_interval_piece (o : mark_order) (m : mark) (pc : piece) =
  let rec helper pc' =
    match pc' with
    | i :: pc'' -> if mark_inside o m i then i else helper pc''
    | [] ->
        failwith
          (Printf.sprintf
             "\n\
             \            The mark specified is not contained in this piece!\n\
             \ \n\
             \            Order: %s\n\n\
             \            Piece: %s\n\n\
             \            Mark: %s\n\n\
             \            " (mark_order_to_str o) (piece_to_str pc)
             (mark_to_str m))
  in
  helper pc.lst

(* Return the suffix of l following a *)
let rec suffix a l =
  match l with
  | a' :: l' -> if a = a' then l' else suffix a l'
  | [] -> failwith "This list does not contain the specified element!"

(* Return the prefix of l before a *)
let prefix a l = List.rev (suffix a (List.rev l))

(* Relax an interval from any smaller piece type p' to type p. This assumes p' contains the interval *)
let relax_interval (o : mark_order) (i : vinterval) : piece =
  match i.lvl with
  | Cake -> form_piece [ i ]
  | Sq pc ->
      let il, ir =
        (mark_interval_piece o i.i.l pc, mark_interval_piece o i.i.r pc)
      in
      if il = ir then form_piece [ { lvl = pc.lvl; i = il } ]
      else
        let intervals = pc.lst |> suffix il |> prefix ir in
        {
          lvl = pc.lvl;
          lst =
            ({ l = i.i.l; r = il.r } :: intervals) @ [ { l = ir.l; r = i.i.r } ];
        }

(* Gets the absolute ends of a piece. Assumes the piece is properly ordered *)
let piece_endpoints pc =
  let rec right_endpoint pc =
    match pc with
    | i :: [] -> i.r
    | _ :: pc' -> right_endpoint pc'
    | [] -> failwith "Empty piece!"
  in
  match pc with
  | h :: _ -> (h.l, right_endpoint pc)
  | [] -> failwith "Empty piece!"

(* This is a structure for keeping track of the list of marks within each interval *)
(* mpo is short for mark_piece_ordering *)
type mark_piece_ordering = (interval * mark list) list

let append_first m l =
  match l with
  | i_list :: l' -> (m :: i_list) :: l'
  | [] -> failwith "Cannot append_first as the list is empty!"

(* Given a piece and marks that happened inside that piece, enumerate all the possibilities of where the marks could lie within the piece *)
let enumerate_mark_placings p o : mark_piece_ordering list =
  let rec helper p o =
    match o with
    | m :: o' -> (
        match p with
        | _ :: p' -> List.map (append_first m) (helper p o') @ helper p' o
        | [] -> [])
    | [] -> [ List.init (List.length p) (fun _ -> []) ]
  in
  List.map (fun placing -> List.combine p placing) (helper p o)

(* Enumerates all the possible ways of inserting the ordered list marks into the slice o_slice *)
let rec fill_in_marks o_slice marks =
  match marks with
  | m :: marks' -> (
      let current =
        List.map (fun filled -> m :: filled) (fill_in_marks o_slice marks')
      in
      match o_slice with
      | m' :: o_slice' ->
          current
          @ List.map (fun filled -> m' :: filled) (fill_in_marks o_slice' marks)
      | [] -> current)
  | [] -> [ o_slice ]

let split o i =
  let rec split o m =
    match o with
    | m' :: o' ->
        if m' = m then ([], o')
        else
          let l', suffix = split o' m in
          (m' :: l', suffix)
    | [] -> failwith "left endpoint of interval not contained in this order!"
  in
  let pre, mid = split o i.l in
  let inside, post = split mid i.r in
  (pre, inside, post)

(* Given an mpo, this enumerates all the possible ways of inserting it into a bigger ordering o *)
let rec insert_mpo o (mpo : (interval * mark list) list) =
  match mpo with
  | (i, marks) :: mpo' ->
      let before_i, contained_in_i, after_i = split o i in
      let filled = fill_in_marks contained_in_i marks in
      List.concat
        (List.map
           (fun o'' ->
             List.map (fun o' -> before_i @ (i.l :: o') @ (i.r :: o'')) filled)
           (insert_mpo after_i mpo'))
  | [] -> [ o ]

(* This gives all the possible ways of inserting an ordering of marks o' from a piece p into an ordering o *)
let all_possible_insertions o p o' =
  let placings_in_p = enumerate_mark_placings p o' in
  List.concat (List.map (insert_mpo o) placings_in_p)

open Format

let kwd = pp_print_string
let mark_formatter f m = kwd f (mark_to_str m)
let interval_formatter f i = kwd f (interval_to_str i)

let rec piece_formatter f (pc : piece) =
  let rec h l =
    match l with
    | i :: [] -> interval_formatter f i
    | i :: l' ->
        interval_formatter f i;
        kwd f ";";
        h l'
    | [] -> ()
  in
  lvl_formatter f pc.lvl;
  pp_print_cut f ();
  pp_open_hbox f ();
  h pc.lst;
  close_box ()

and lvl_formatter f lvl =
  match lvl with
  | Cake -> ()
  | Sq pc ->
      kwd f "{";
      piece_formatter f pc;
      kwd f "} "

let rec mark_order_formatter f o =
  match o with
  | m :: [] -> mark_formatter f m
  | m :: o' ->
      mark_formatter f m;
      kwd f " ≤ ";
      mark_order_formatter f o'
  | [] -> ()





(* Test cases *)


let o_test = [L ; U 1; U 2; U 3; R] 

let i1_test = {l = L; r = U 2}
let i2_test = {l = U 1; r = U 3}

let p_test = [i1_test ; i2_test]

let refined_p_test = refine o_test p_test

let atomic_i1_test = atomic_interval_representation o_test i1_test
let atomic_i2_test = atomic_interval_representation o_test i2_test

let atomic_p_test = atomic_piece_representation o_test refined_p_test

let p2_test = atomic_i1_test @ atomic_i2_test
let refined_p2_test = refine o_test p2_test

let atomic_p2_test = atomic_piece_representation o_test refined_p2_test

let _ = assert (refined_p_test = [{l = L; r = U 3}])
let _ = assert (atomic_i1_test = [{l = L; r = U 1}; {l = U 1; r = U 2}])
let _ = assert (atomic_i2_test = [{l = U 1; r = U 2}; {l = U 2; r = U 3}])
let _ = assert (refined_p2_test = refined_p_test)
let _ = assert (atomic_p2_test = atomic_p_test)
