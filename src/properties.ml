open List
open Formula

let geq a b = Pred (Geq, a, b)
let leq a b = geq b a
let eq a b = Pred (Eq, a, b)
let plus a b : term = Op (A Plus, [ a; b ])
let minus a b : term = Minus (a, b)
let neg a : formula = Neg a
let zero : term = Val (Real (0, None))
let one : term = Val (Real (1, None))

let rec possible_places max =
  if max > 0 then possible_places (max - 1) @ [ max ] else [ 0 ]

let rec sum term_list : term =
  match term_list with [] -> zero | h :: [] -> h | h :: t -> plus h (sum t)

let piece_value n piece =
  let s = sort_of_term piece in
  match s with
  | Tup s_list ->
      let index = possible_places (length s_list - 1) in
      sum (map (fun k -> V (n, Proj (k, piece))) index)
  | Interval -> V (n, piece)
  | Piece -> V (n, piece)
  | _ -> failwith "Wrong sort!"

(* Agent n prefers (weakly) a to b*)
let prefer n a b = geq (piece_value n a) (piece_value n b)

(* Agent n's allocation *)
let alloc_n n alloc : term = Proj (n - 1, alloc)

(* agent n envies agent n' *)
let envy n n' alloc = neg (prefer n (alloc_n n alloc) (alloc_n n' alloc))
let pairs l1 l2 = concat (map (fun a -> map (fun b -> (a, b)) l2) l1)

(* There is envy *)
let envy_any agent_count alloc =
  let agent_list = List.init agent_count (fun i -> i + 1) in
  let agent_pairs =
    filter (fun (n, n') -> not (n = n')) (pairs agent_list agent_list)
  in
  Or (map (fun (n, n') -> envy n n' alloc) agent_pairs)

let no_prop _ _ = True



(* 
   #################




   CUSTOM PROPERTIES




   #################
*)


(* Write as seen fit. Functions above may be helpful *)
let custom agent_count allocation = no_prop agent_count allocation












(* Valuation axioms. Unneeded for reduced verification, only for unreduced. *)
let implies a b = Implies (a, b)
let v_ge_0 i n = geq (V (n, i)) zero
let v_le_1 i n = geq one (V (n, i))

let v_monotone i i' n =
  implies
    (And [ geq (LeftEnd i) (LeftEnd i'); geq (RightEnd i') (RightEnd i) ])
    (geq (V (n, i')) (V (n, i)))

let v_additive i i' n =
  implies
    (eq (RightEnd i) (LeftEnd i'))
    (eq
       (plus (V (n, i)) (V (n, i')))
       (V (n, Interval (LeftEnd i, RightEnd i'))))

let no_point_mass i n =
  implies (eq (RightEnd i) (LeftEnd i)) (eq (V (n, i)) zero)

let v_init_1 n = eq (V (n, Interval (zero, one))) one

let sum_1 i n =
  eq
    (plus
       (V (n, Interval (zero, LeftEnd i)))
       (plus (V (n, i)) (V (n, Interval (RightEnd i, one)))))
    one

let reverse_monotone_l i i' n =
  implies
    (And [ geq (V (n, i)) (V (n, i')); geq (LeftEnd i) (LeftEnd i') ])
    (geq (RightEnd i) (RightEnd i'))

let reverse_monotone_r i i' n =
  implies
    (And [ geq (V (n, i)) (V (n, i')); geq (RightEnd i') (RightEnd i) ])
    (geq (LeftEnd i') (LeftEnd i))

let assumption_n n =
  let i, i' = (Var ([ 0 ], Interval), Var ([ 1 ], Interval)) in
  ForAll
    ( [ ([ 0 ], Interval); ([ 1 ], Interval) ],
      implies
        (And
           [
             geq one (RightEnd i);
             geq (LeftEnd i) zero;
             geq (RightEnd i) (LeftEnd i);
             geq one (RightEnd i');
             geq (LeftEnd i') zero;
             geq (RightEnd i') (LeftEnd i');
           ])
        (And
           [
             v_ge_0 i n;
             v_le_1 i n;
             v_monotone i i' n;
             v_additive i i' n;
             no_point_mass i n;
             v_init_1 n;
             (*reverse_monotone_l i i' n;
               reverse_monotone_r i i' n;*)
           ]) )
