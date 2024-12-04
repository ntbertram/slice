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

(* Converting between objects and their terms *)
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

  (* Left endpoint associated with given agent *)
let agent_pt_t n (pt : point) = Pt (P (n, (lvl_to_term pt.lvl, pt.pt)))

let rec sum term_list : term =
  match term_list with [] -> zero | h :: [] -> h | h :: t -> plus h (sum t)

let ( -- ) a b = Minus (a, b)

let atomic_interval_pu_value n vi = 
    let m = point_to_term {lvl = vi.lvl; pt = vi.i.r} in
    let lm = agent_pt_t n {lvl = vi.lvl; pt = vi.i.r} in
    m -- lm

let atomic_piece_value (red : bool) n (os : (level * mark_order) list) (pc : piece) =
    let o =
        match List.assoc_opt pc.lvl os with Some o -> o | None -> [ L; R ]
    in
    pc.lst 
    |> refine o
    |> (atomic_piece_representation o)
    |> List.map (fun i -> {lvl = pc.lvl; i = i})
    |> 
    begin 
        if red then 
            (List.map (atomic_interval_pu_value n)) 
        else 
            (List.map (fun vi -> V (n, (interval_to_term vi))))
    end
    |> sum


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


let rec replace_vals red o t =
  match t with
  | Val (Real _) -> t
  | Pt _ -> t
  | Minus (t1, t2) -> Minus (replace_vals red o t1, replace_vals red o t2)
  | Op (A op, [ t1; t2 ]) -> Op (A op, [ replace_vals red o t1; replace_vals red o t2 ])
  | V (n, t) -> t |> piece_term_to_piece |> atomic_piece_value red n o
  | _ ->
      failwith
        (p "There should be no additional cases here. Recieved %s."
           (term_to_str t))

let replace_vals_formula red m_ordered f =
  f_formula (fun x -> x) (replace_vals red m_ordered) f

  (* Formula simplification (Removes redundant symbols and converts boolean terms to formulas) *)
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

(* Building the ordering on the marks *)
let rec divide_formula_substitute divides =
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

(* Gives the constraint on the value of the cake at a smaller level *)
let value_piece_constraint n (lvl : level) o =
  let v pc = V (n, piece_to_term pc) in
  match lvl with
  | Cake -> True
  | Sq pc -> v pc == atomic_piece_value true n [(lvl, o)] {lvl = lvl; lst = [{l = L; r = R}]}

(* *)
let all_value_piece_constraints os agent_list =
  let g n (lvl, o) = value_piece_constraint n lvl o in
  let f n = new_and (List.map (g n) os) in
  new_and (List.map f agent_list)

let closed_cnstr e = cnstr (e, []) 0 []


(* Gives the mark orderings as formulas *)
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


(*Combining into one formula *)
let build_path_formula (red : bool) (e : path) prop =
  let c, rho, _, divides = closed_cnstr e in
  let mark_orders =
    List.map (fun (lvl, l) -> (lvl, order_marks l)) (assoc_list_factor divides)
  in
  let agent_count =
    match sort_of_term rho with Tup l -> length l | _ -> failwith "Not sure"
  in
  let simplified_constraint =
      c |> formula_substitute |> replace_vals_formula red mark_orders
  in
  let simplified_property =
      prop agent_count rho |> formula_substitute |> replace_vals_formula red mark_orders
  in
  let specific_assumptions = 
        if red then
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
          let simplified_value_constraints = 
              value_constraints |> replace_vals_formula red mark_orders
          in
          new_and (simplified_value_constraints :: agent_valuations)
      else
          let mark_order_formula = mark_orders_formula mark_orders in
          let general_valuation_assumptions =
            new_and (List.map assumption_n (List.init agent_count (fun i -> i + 1)))
          in
          new_and [mark_order_formula; general_valuation_assumptions]
  in new_and [specific_assumptions; simplified_property; simplified_constraint]

let verification red e prop =
  let path_list = expression_to_path_list e in
  let path_formula_list =
    map (fun p -> build_path_formula red p prop) path_list
  in
  Or path_formula_list


let output_formula_to_file file_name f =
    let fmt = file_name |> open_out |> Format.formatter_of_out_channel in
    formula_formatter fmt f
