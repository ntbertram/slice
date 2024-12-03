open List
open Ast
open Path
open Piece
open Formula
open Properties

(* Translation *)

(* Real formula translation *)
let geq a b = Pred (Geq, a, b)
let leq a b = geq b a
let eq a b = Pred (Eq, a, b)
let plus a b : term = Op (A Plus, [ a; b ])
let minus a b : term = Minus (a, b)
let zero : term = Val (Real (0, None))
let one : term = Val (Real (1, None))
let cake_piece = Piece [ Interval (Pt (M (Cake, L)), Pt (M (Cake, R))) ]

let rec interval_term_to_interval t =
  match t with
  | Interval (t1, t2) ->
      let l, r = (real_term_to_point t1, real_term_to_point t2) in
      form_interval l r
  | _ -> failwith "Cannot convert to interval_term."

and piece_term_to_piece t =
  match t with
  | Piece t_list -> form_piece (List.map interval_term_to_interval t_list)
  | _ -> failwith (p "Cannot turn term %s into a piece!" (term_to_str t))

and pc_t_to_lvl pc_t : level =
  match pc_t with Cake -> Cake | Sq t -> Sq (piece_term_to_piece t)

and real_term_to_point t =
  match t with
  | Pt (M (pc_t, m)) -> { lvl = pc_t_to_lvl pc_t; pt = m }
  | _ -> failwith "Cannot convert this term to a point!"

let rec point_to_term (pt : point) = Pt (M (lvl_to_term pt.lvl, pt.pt))

and lvl_to_term lvl =
  match lvl with Cake -> Cake | Sq pc -> Sq (piece_to_term pc)

and piece_to_term pc =
  let i_list = List.map (fun i -> { lvl = pc.lvl; i }) pc.lst in
  Piece ((List.map interval_to_term) i_list)

and interval_to_term (i : vinterval) =
  let l, r =
    ( point_to_term { lvl = i.lvl; pt = i.i.l },
      point_to_term { lvl = i.lvl; pt = i.i.r } )
  in
  Interval (l, r)

let agent_pt_t n (pt : point) = Pt (P (n, (lvl_to_term pt.lvl, pt.pt)))

(*Needs a bit of work *)
(*
let contained (p1 : piece) (p2 : piece) =
    List.filter (fun i -> List.exists (fun i' -> i = i') p2) p1
*)

let rec sum term_list : term =
  match term_list with [] -> zero | h :: [] -> h | h :: t -> plus h (sum t)

let ( -- ) a b = Minus (a, b)

let points_in_interval o i =
  if i.l = i.r then [] else (o |> prefix i.r |> suffix i.l) @ [ i.r ]

let rec integrate (curr : mark list) mlist =
  let contains m' =
    List.fold_left (fun b m -> if m = m' then true else b) false
  in
  match mlist with
  | m :: mlist' ->
      if contains m curr then integrate curr mlist'
      else integrate (m :: curr) mlist'
  | [] -> curr

(* Get the value of a piece p of type p' *)
let value_piece n (os : (level * mark_order) list) (pc : piece) =
  let o =
    match List.assoc_opt pc.lvl os with Some o -> o | None -> [ L; R ]
  in
  let points =
    List.fold_left
      (fun curr i -> integrate curr (points_in_interval o i))
      [] pc.lst
  in
  let mt m = point_to_term { lvl = pc.lvl; pt = m } in
  let mpt m = agent_pt_t n { lvl = pc.lvl; pt = m } in
  sum (List.map (fun m -> mt m -- mpt m) points)

let value_piece_no_red n (os : (level * mark_order) list) (pc : piece) =
  let o =
    match List.assoc_opt pc.lvl os with Some o -> o | None -> [ L; R ]
  in
  let points =
    List.fold_left
      (fun curr i -> integrate curr (points_in_interval o i))
      [] pc.lst
  in
  let mt m = point_to_term { lvl = pc.lvl; pt = m } in
  let rec get_left left m o =
    match o with
    | m' :: o' -> if m = m' then left else get_left m' m o'
    | [] -> failwith "Mark not contained within mark order"
  in
  let leftmt m =
    let ml = get_left L m o in
    point_to_term { lvl = pc.lvl; pt = ml }
  in
  sum (List.map (fun m -> V (n, Interval (leftmt m, mt m))) points)

(*List.map (interval_value n pc.lvl o) pc.lst *)

(* Obtain the value of the interval that you have *)
let interval_value n lvl o i = value_piece n [ (lvl, o) ] { lvl; lst = [ i ] }

(* Converts function symbol riddled formulas to just those containing real numbers, free variables, and valuation function symbols *)
let rec real_replacement t =
  match t with
  | LeftEnd t -> (
      match interval_replacement t with
      | Interval (t1, _) -> real_replacement t1
      | _ -> failwith "no")
  | RightEnd t -> (
      match interval_replacement t with
      | Interval (_, t2) -> real_replacement t2
      | _ -> failwith "no")
  | Proj (n, t) -> (
      match tuple_replacement t with
      | Tup t_list -> nth t_list n
      | _ -> failwith "no")
  | Minus (t1, t2) -> Minus (real_replacement t1, real_replacement t2)
  | Pt pt_t ->
      let replace_mark_term (pc_t, m) =
        let replaced_pc_t =
          match pc_t with Cake -> Cake | Sq t -> Sq (piece_replacement t)
        in
        (replaced_pc_t, m)
      in
      let pt =
        match pt_t with
        | M mt -> M (replace_mark_term mt)
        | P (i, mt) -> P (i, replace_mark_term mt)
      in
      Pt pt
  | V (n, t) -> (
      match sort_of_term t with
      | Interval -> V (n, Piece [ interval_replacement t ])
      | Piece -> V (n, piece_replacement t)
      | _ -> failwith "V can only take interval or piece as arguments!")
  | Val (Real (n, d)) -> Val (Real (n, d))
  | Op (A op, [ t1; t2 ]) ->
      Op (A op, [ real_replacement t1; real_replacement t2 ])
  | _ -> failwith (p "bad translation: received %s" (term_to_str t))

and interval_replacement t =
  match t with
  | Proj (n, t) -> (
      match tuple_replacement t with
      | Tup t_list -> nth t_list n
      | _ -> failwith "Not working")
  | Interval (t1, t2) -> Interval (real_replacement t1, real_replacement t2)
  | _ -> failwith "Not supposed to happen"

and piece_replacement t =
  match t with
  | Piece t_list -> Piece (map interval_replacement t_list)
  | Proj (n, t) -> (
      match tuple_replacement t with
      | Tup t_list -> nth t_list n
      | _ -> failwith "Not working")
  | _ -> failwith "Not supposed to happena"

and tuple_replacement t =
  match t with
  | Tup t_list ->
      Tup
        (map
           (fun t ->
             match sort_of_term t with
             | Real -> real_replacement t
             | Tup _ -> tuple_replacement t
             | Interval -> interval_replacement t
             | Piece -> piece_replacement t
             | Num -> t
             | Bool -> t
             | _ -> failwith "Not supposed to happen")
           t_list)
  | Proj (n, t) -> (
      match tuple_replacement t with
      | Tup t_list -> nth t_list n
      | _ -> failwith "no")
  | _ -> failwith (p "not supposed to happen. Received %s" (term_to_str t))

and term_replacement t =
  match sort_of_term t with
  | Real -> real_replacement t
  | Tup _ -> tuple_replacement t
  | Interval -> interval_replacement t
  | Piece -> piece_replacement t
  | _ -> failwith "Not supposed to happen."

(* Produces substring of l that starts with a and ending with b, not including a *)
let substring l a b =
  let rec post_substring l b =
    match l with
    | h :: t -> if h = b then [ b ] else h :: post_substring t b
    | [] -> []
  in
  let rec pre_substring l a b =
    match l with
    | h :: t -> if h = a then post_substring t b else pre_substring t a b
    | [] -> []
  in
  pre_substring l a b

let rec replace_vals o t =
  match t with
  | Val (Real _) -> t
  | Pt _ -> t
  | Minus (t1, t2) -> Minus (replace_vals o t1, replace_vals o t2)
  | Op (A op, [ t1; t2 ]) -> Op (A op, [ replace_vals o t1; replace_vals o t2 ])
  | V (n, t) -> t |> piece_term_to_piece |> value_piece n o
  | _ ->
      failwith
        (p "There should be no additional cases here. Recieved %s."
           (term_to_str t))

let replace_vals_formula m_ordered f =
  f_formula (fun x -> x) (replace_vals m_ordered) f

let rec replace_vals_no_red o t =
  match t with
  | Val (Real _) -> t
  | Pt _ -> t
  | Minus (t1, t2) -> Minus (replace_vals_no_red o t1, replace_vals_no_red o t2)
  | Op (A op, [ t1; t2 ]) ->
      Op (A op, [ replace_vals_no_red o t1; replace_vals_no_red o t2 ])
  | V (n, t) -> (
      match sort_of_term t with
      | Piece -> t |> piece_term_to_piece |> value_piece_no_red n o
      | Interval -> t
      | s ->
          failwith
            (p
               "Sort mismatch. V expexts sorts piece or interval. Received \
                sort %s."
               (sort_to_str s)))
  | _ ->
      failwith
        (p "There should be no additional cases here. Recieved %s."
           (term_to_str t))

let replace_vals_formula_no_red m_ordered f =
  f_formula (fun x -> x) (replace_vals_no_red m_ordered) f

let rec formula_substitute f =
  match f with
  | True -> True
  | False -> False
  | Pred (cop, t1, t2) -> pred_sub (cop, t1, t2)
  | Implies (f1, f2) -> Implies (formula_substitute f1, formula_substitute f2)
  | And f_list -> new_and (map formula_substitute f_list)
  | Or f_list -> Or (map formula_substitute f_list)
  | Neg f -> Neg (formula_substitute f)
  | ForAll (t_list, f) -> ForAll (t_list, formula_substitute f)
  | Exists (t_list, f) -> ForAll (t_list, formula_substitute f)
  | _ -> failwith "Not allowed"

and pred_sub p =
  match p with
  | Eq, t1, t2 -> (
      match (sort_of_term t1, sort_of_term t2) with
      | Interval, Interval ->
          let l1, r1, l2, r2 =
            ( real_replacement (LeftEnd t1),
              real_replacement (RightEnd t1),
              real_replacement (LeftEnd t2),
              real_replacement (RightEnd t2) )
          in
          And [ Pred (Eq, l1, l2); Pred (Eq, r1, r2) ]
      | Real, Real -> Pred (Eq, real_replacement t1, real_replacement t2)
      | Val, Val -> Pred (Eq, real_replacement t1, real_replacement t2)
      | s1, s2 ->
          failwith
            (Printf.sprintf "Sorts %s and %s with predicate (=) is not allowed."
               (sort_to_str s1) (sort_to_str s2)))
  | Geq, t1, t2 -> Pred (Geq, real_replacement t1, real_replacement t2)

(* Given the current mark ordering, replace valuations with sums of real numbers *)
let rec build_agent_valuation n lvl prev (o : mark list) =
  let f = build_agent_valuation n lvl in
  match o with
  | L :: o' ->
      let pt = { lvl; pt = L } in
      f (point_to_term pt) o'
  | R :: [] ->
      let pt = { lvl; pt = R } in
      let rmpt, rmt = (agent_pt_t n pt, point_to_term pt) in
      [ leq rmpt rmt; leq prev rmpt ]
  | m :: o' ->
      let pt = { lvl; pt = m } in
      let mpt, mt = (agent_pt_t n pt, point_to_term pt) in
      leq mpt mt :: leq prev mpt :: f mt o'
  | _ -> failwith (p "Woops! Not supposed to happen.")
(*(term_to_str (hd m_list)) (term_to_str (hd (tl m_list))))*)

(* Building the ordering on the marks *)
let rec divide_formula_substitute divides =
  (* let f t = real_term_to_point (real_replacement t) in *)
  match divides with
  | (t1, t2, t3) :: t -> (t1, t2, t3) :: divide_formula_substitute t
  | [] -> []

let rec insert_mark m1 m3 m2 l =
  if List.fold_left (fun b m -> if m = m2 then true else b) false l then l
  else
    match l with
    | h1 :: h2 :: t -> (
        match (h1 = m1, h2 = m3) with
        | true, true -> h1 :: m2 :: h2 :: t
        | false, false -> h1 :: insert_mark m1 m3 m2 (h2 :: t)
        | _ -> failwith "Not consecutive marks!")
    | _ :: [] -> failwith "Not supposed to happen"
    | [] -> failwith "Also not supposed to happen"

let rec order_marks divides =
  match divides with
  | (m1, m2, m3) :: t -> insert_mark m1 m3 m2 (order_marks t)
  | [] -> [ L; R ]

let assoc_list_factor (l : ('a * 'b) list) : ('a * 'b list) list =
  let rec add l_new a b =
    match l_new with
    | (a', l') :: l_new' ->
        if a = a' then (a', b :: l') :: l_new' else (a', l') :: add l_new' a b
    | [] -> [ (a, [ b ]) ]
  in
  let rec h l = match l with (a, b) :: l' -> add (h l') a b | [] -> [] in
  h l

(* Cases *)

(* Counter for counting indexed by agents *)
let rec inc n counter =
  let current_counter, remaining_counters =
    match counter with h :: t -> (h, t) | [] -> (0, [])
  in
  if n > 0 then current_counter :: inc (n - 1) remaining_counters
  else (current_counter + 1) :: remaining_counters

let rec count n counter =
  match counter with h :: t -> if n > 0 then count (n - 1) t else h | [] -> 0

let rec subs_divides l t_new d_list =
  match d_list with
  | (t1, t2, t3) :: t ->
      (subs_term l t_new t1, subs_term l t_new t2, subs_term l t_new t3)
      :: subs_divides l t_new t
  | [] -> []

let ( >> ) f g x = g (f x)
let ( << ) f g x = f (g x)

(* Produces the constraint of an expression *)
let rec cnstr ((e : path), (env : (int list * term) list)) k divides =
  let ( == ) a b = Pred (Eq, a, b) in
  let ( * ) a b = Op (A Times, [ a; b ]) in
  match e with
  | Divide (e1, e2) ->
      let f1, rho1, k1, divides1 = cnstr (e1, env) k [] in
      let f2, rho2, k2, divides2 = cnstr (e2, env) k1 [] in
      let f =
        new_and
          [
            (*Pred (Cop (Geq, rrho1, rho2)); Pred (Cop (Geq, rho2, lrho1));*)
            f1;
            f2;
          ]
      in
      let l, r =
        match rho1 with Interval (l, r) -> (l, r) | _ -> failwith "No"
      in
      let ptl, pts, ptr =
        (real_term_to_point l, real_term_to_point rho2, real_term_to_point r)
      in
      assert (ptl.lvl = pts.lvl && pts.lvl = ptr.lvl);
      let rho = Tup [ Interval (l, rho2); Interval (rho2, r) ] in
      ( f,
        rho,
        k2,
        ((ptl.lvl, (ptl.pt, pts.pt, ptr.pt)) :: divides2) @ divides1 @ divides
      )
  | Let (var_list, e1, e2) ->
      (*let typ = typ_of_path env e1 in *)
      let f1, rho1, k1, divides1 = cnstr (e1, env) k [] in
      let env' =
        match var_list with
        | [ x ] -> (x, rho1) :: env
        | _ ->
            let t_list =
              match rho1 with
              | Tup t_list -> t_list
              | _ ->
                  List.init (List.length var_list - 1) (fun i -> Proj (i, rho1))
            in
            List.combine var_list t_list @ env
      in
      let f2, rho2, k2, divides2 = cnstr (e2, env') k1 [] in
      let f = new_and [ f1; f2 ] in
      (f, rho2, k2, divides2 @ divides1 @ divides)
  | Mark (n, e1, e2) ->
      let f1, rho1, k1, divides1 = cnstr (e1, env) k [] in
      let f2, rho2, k2, divides2 = cnstr (e2, env) k1 [] in
      let i = interval_term_to_interval rho1 in
      let m = U (k2 + 1) in
      let i' = { lvl = i.lvl; i = { l = i.i.l; r = m } } in
      let i'term = interval_to_term i' in
      let rho = point_to_term { lvl = i.lvl; pt = m } in
      let f = new_and [ f1; f2; rho2 == V (n, Piece [ i'term ]) ] in
      (f, rho, k2 + 1, divides2 @ divides1 @ divides)
  | MarkW (n, e1, e2) ->
      let f1, rho1, k1, divides1 = cnstr (e1, env) k [] in
      let f2, rho2, k2, divides2 = cnstr (e2, env) k1 [] in
      let i = interval_term_to_interval rho1 in
      let m = U (k2 + 1) in
      let i' = { lvl = i.lvl; i = { l = i.i.l; r = m } } in
      let iterm = interval_to_term i in
      let i'term = interval_to_term i' in
      let rho = point_to_term { lvl = i.lvl; pt = m } in
      let weighted_value = rho2 * V (n, Piece [ iterm ]) in
      let f = new_and [ f1; f2; V (n, Piece [ i'term ]) == weighted_value ] in
      (f, rho, k2 + 1, divides2 @ divides1 @ divides)
  | Eval (n, e) ->
      let f1, rho1, k1, divides1 = cnstr (e, env) k [] in
      let f = f1 in
      let rho = V (n, rho1) in
      (f, rho, k1, divides1 @ divides)
  | Piece e_list ->
      let f, rho, k, divides_list = cnstr_tup env e_list ([], [], k, []) in
      let f = new_and f in
      let rho = Piece rho in
      (f, rho, k, divides_list @ divides)
  | Union (e1, e2) ->
      let e1_list, e2_list =
        match (e1, e2) with
        | Piece e1_list, Piece e2_list -> (e1_list, e2_list)
        | _ -> failwith "Not supposed to happen"
      in
      let e_list = e1_list @ e2_list in
      let f, rho, k, divides_list = cnstr_tup env e_list ([], [], k, []) in
      let f = new_and f in
      let rho = Piece rho in
      (f, rho, k, divides_list @ divides)
  | Squeeze e ->
      let f, rho, k, divides1 = cnstr (e, env) k [] in
      let pc = piece_term_to_piece rho in
      let i_new = { lvl = Sq pc; i = { l = L; r = R } } in
      (f, interval_to_term i_new, k, divides1 @ divides)
  | Tuple e_list ->
      let f, rho, k, divides_list = cnstr_tup env e_list ([], [], k, []) in
      let f = new_and f in
      let rho = Tup rho in
      (f, rho, k, divides_list @ divides)
  | Assert (e1, e2) ->
      let f1, rho1, k1, divides1 = cnstr (e1, env) k [] in
      let f2, rho2, k2, divides2 = cnstr (e2, env) k1 [] in
      let f = new_and [ bool_to_formula rho1; f1; f2 ] in
      let rho = rho2 in
      (f, rho, k2, divides1 @ divides2 @ divides)
  | Op (op, e_list) ->
      let f, rho, k, divides_list = cnstr_tup env e_list ([], [], k, []) in
      let f = new_and f in
      let rho = Op (op, rho) in
      (f, rho, k, divides_list @ divides)
  | Cake ->
      (True, interval_to_term { lvl = Cake; i = { l = L; r = R } }, k, divides)
  | Val v -> (True, Val v, k, divides)
  | Var l ->
      (*let rho = Var (l, typ_of_exp env (Var l)) in*)
      let rho = List.assoc (var_id l) env in
      (True, rho, k, divides)

and cnstr_tup env remaining prev =
  match remaining with
  | h :: t ->
      let f_prev, rho_prev, k_prev, divides = prev in
      let f, rho, k, divides1 = cnstr (h, env) k_prev [] in
      let current =
        (f_prev @ [ f ], rho_prev @ [ rho ], k, divides1 @ divides)
      in
      cnstr_tup env t current
  | [] -> prev

let ( >= ) a b = geq a b
let ( <= ) a b = leq a b
let ( == ) a b = eq a b

let value_piece_constraint n (lvl : level) o =
  let v pc = V (n, piece_to_term pc) in
  match lvl with
  | Cake -> True
  | Sq pc -> v pc == interval_value n lvl o { l = L; r = R }

let all_value_piece_constraints os agent_list =
  let g n (lvl, o) = value_piece_constraint n lvl o in
  let f n = new_and (List.map (g n) os) in
  new_and (List.map f agent_list)

let closed_cnstr e = cnstr (e, []) 0 []

(*Combining into one formula *)
let build_path_formula_with_f (e : path) f =
  let c, rho, _, divides = closed_cnstr e in
  let mark_orders =
    List.map (fun (lvl, l) -> (lvl, order_marks l)) (assoc_list_factor divides)
  in
  let agent_count =
    match sort_of_term rho with Tup l -> length l | _ -> failwith "Not sure"
  in
  let agent_list = List.tl (List.init (agent_count + 1) (fun i -> i)) in
  let agent_val_formula lvl order n = build_agent_valuation n lvl zero order in
  let agent_valuations =
    concat
      (List.map
         (fun (lvl, order) ->
           concat (map (agent_val_formula lvl order) agent_list))
         mark_orders)
  in
  let value_constraints = all_value_piece_constraints mark_orders agent_list in
  let real_c = replace_vals_formula mark_orders (formula_substitute c) in
  let real_f = replace_vals_formula mark_orders (formula_substitute (f rho)) in
  let real_vc = replace_vals_formula mark_orders value_constraints in
  new_and (real_f :: real_c :: real_vc :: agent_valuations)

(* The following are irrelevent to artifact *)
let build_path_formula_vc (e : path) =
  let _, rho, _, divides = closed_cnstr e in
  let mark_orders =
    List.map (fun (lvl, l) -> (lvl, order_marks l)) (assoc_list_factor divides)
  in
  let agent_count =
    match sort_of_term rho with Tup l -> length l | _ -> failwith "Not sure"
  in
  let agent_list = List.tl (List.init (agent_count + 1) (fun i -> i)) in
  let value_constraints = all_value_piece_constraints mark_orders agent_list in
  new_and [ replace_vals_formula mark_orders value_constraints ]

let check_vc e =
  let path_list = expression_to_path_list e in
  let path_formula_list = map (fun p -> build_path_formula_vc p) path_list in
  Or path_formula_list

let build_path_formula e = build_path_formula_with_f e (fun _ -> True)

let complete_real_constraint (e : expression) =
  let path_list = expression_to_path_list e in
  let path_formula_list = map (fun p -> build_path_formula p) path_list in
  Or path_formula_list

let check_property e f =
  let path_list = expression_to_path_list e in
  let path_formula_list =
    map (fun p -> build_path_formula_with_f p f) path_list
  in
  Or path_formula_list

let mark_orders_formula ol =
  let rec mark_order_formula o =
    match o with
    | m :: m' :: o' -> leq m m' :: mark_order_formula (m' :: o')
    | _ -> []
  in
  let replace_lvls lvl o = List.map (fun m -> { lvl; pt = m }) o in
  new_and
    (List.map
       (fun (lvl, o) ->
         o |> replace_lvls lvl |> List.map point_to_term |> mark_order_formula
         |> new_and)
       ol)

let build_path_formula_with_f_no_red (e : path) f =
  let c, rho, _, divides = closed_cnstr e in
  let mark_orders =
    List.map (fun (lvl, l) -> (lvl, order_marks l)) (assoc_list_factor divides)
  in
  let agent_count =
    match sort_of_term rho with Tup l -> length l | _ -> failwith "Not sure"
  in
  (*let agent_list = List.init agent_count (fun i -> i + 1) in
    let agent_val_formula lvl order n = build_agent_valuation n lvl zero order in*)
  (*let agent_valuations =
      concat
        (List.map
           (fun (lvl, order) ->
             concat (map (agent_val_formula lvl order) agent_list))
           mark_orders)
    in*)
  let c = replace_vals_formula_no_red mark_orders (formula_substitute c) in
  let f =
    replace_vals_formula_no_red mark_orders (formula_substitute (f rho))
  in
  let mark_order_formula = mark_orders_formula mark_orders in
  let val_assumptions =
    new_and (List.map assumption_n (List.init agent_count (fun i -> i + 1)))
  in
  new_and [ mark_order_formula; f; c; val_assumptions ]

let check_property_no_red e f =
  let path_list = expression_to_path_list e in
  let path_formula_list =
    map (fun p -> build_path_formula_with_f_no_red p f) path_list
  in
  let f = Or path_formula_list in f
(*
let build_formula dl file_name =
    let e = build_expression dl file_name in
    let (f, t) = qsr_to_formula_v (e_to_qsr [] [] ([], e)) in
    ((pre_foe_to_foe [] f), t)
*)
(*
let constraint_to_file file_name c =
    let out = open_out file_name in
    output_string out (foe_to_str c) ; flush out
*)
