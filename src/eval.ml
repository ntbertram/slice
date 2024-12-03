open Basic
open Ast
let geq = real_geq
let leq r r' = geq r' r
let plus = aop_real Plus
let (+.) a b = plus a b
let (>=) a b = geq a b
let (<=) a b = leq a b
let (-.) a b = minus a b
let ( *. ) a b = aop_real Times a b



(* Reconstructs the valuation function given a piece to consider *)
let rec val_lift v (i : vinterval) = 
    match i.lvl with
    | Cake  -> v i.i
    | Sq pc -> 
        let lvl = pc.lvl in
        let rec h pc l r = 
            match pc with 
            | i' :: pc' -> 
                    begin match cont l i', cont r i' with
                    | Inside, Inside -> val_lift v {lvl = lvl; i = {l = l; r = r}}
                    | Left, Inside   -> val_lift v {lvl = lvl; i = {l = i'.l; r = r}} 
                    | Inside, Right  -> val_lift v {lvl = lvl; i = {l = l; r = i'.r}} +. h pc' i'.r r
                    | Left, Right    -> val_lift v {lvl = lvl; i = {l = i'.l; r = i'.r}} +. h pc' i'.r r
                    | Right, Right   -> h pc' l r
                    | Left, Left     -> (0, None)
                    | _ -> failwith "Not possible"
                    end
            | [] -> (0, None)
        in 
        let l, r = unsqueeze_pt {lvl = i.lvl; pt = i.i.l}, unsqueeze_pt {lvl = i.lvl; pt = i.i.r} in
        h pc.pc l.pt r.pt

let v_list v p = aop_real_list Plus (List.map v p)

(* Provide valuation at the same level of mark  *)
(* This takes in a mark function and raises it to a mark function on the piece provided *)
let rec mark_lift v m (i : vinterval) (a : real) = 
    match i.lvl with
    | Cake  -> {lvl = Cake; pt = m i.i a}
    | Sq pc ->
        assert (val_lift v (squeeze_piece pc) >= a);
        let lvl = pc.lvl in
        let rec h pc mark_value =
            match pc with
            | i' :: pc' -> 
                    let i' = {lvl = lvl; i = i'} in
                    if val_lift v i' >=  mark_value then
                        mark_lift v m i' mark_value
                    else
                        h pc' (mark_value -. val_lift v i') 
            | []        -> failwith "Should never happen"
        in
        let pc_i = unsqueeze_i i in
        let point = h pc_i.pc a in
        new_point pc point


(* Short format for printing *)
let p = Printf.sprintf

let rec eval env (exp : expression) (valns : agent_valns) : value =
    match exp with
    | Val v                     -> v
    | Cake                      -> Interval {lvl = Cake; i = {l = (0, None); r = (1, None)}}
    | Var l                     -> List.assoc (var_id l) env
    | Divide (e1, e2)           -> eval_divide(eval env e1 valns, eval env e2 valns)
    | IfThenElse (b1, e1, e2)   -> eval_ifthenelse(eval env b1 valns, env, valns, e1, e2)
    | Let (var_list, e1, e2)           -> 
            begin (*try*)
            match eval env e1 valns with
            | Tup val_list ->
                    let env = (List.combine var_list val_list) @ env in
                    eval env e2 valns
            | v            ->  
                    match var_list with
                    | [x] -> eval ((x, v) :: env) e2 valns
                    | _   -> print_endline "test2" ; failwith "The number of variables and number of assigned values do not line up"
            (*with 
            _ -> 
                (*print_endline "test"; (failwith "The number of variables and number of assigned values do not line up")*) *)
            end

    | Op (op, elist)            -> apply_op op (List.map (fun e -> eval env e valns) elist)


    | Tuple e_list              -> let ev e = eval env e valns in Tup (List.map ev e_list)
    | Eval (e0, e1)             -> eval_eval(eval env e0 valns, eval env e1 valns, valns)
    | Mark (e0, e1, e2)         -> eval_mark(eval env e0 valns, eval env e1 valns, eval env e2 valns, valns)
    | MarkW (e0, e1, e2)        -> eval_markw(eval env e0 valns, eval env e1 valns, eval env e2 valns, valns)
    | Piece e_list              -> let ev e = eval env e valns in  
                                   let v_list = List.map ev e_list in
                                   eval_piece v_list
    | Union (e1, e2)            -> eval_union (eval env e1 valns) (eval env e2 valns)
    | Squeeze e                 -> eval_squeeze (eval env e valns)
    and eval_union v1 v2 = 
        match v1, v2 with 
        | Piece pc1, Piece pc2 -> 
                assert (pc1.lvl = pc2.lvl);
                Piece {lvl = pc1.lvl; pc = pc1.pc @ pc2.pc}
        | _ -> failwith "Union of non-pieces"
    and eval_piece v_list =
        let get_piece =
            fun v -> match v with Interval i -> i | _ -> failwith "Cannot form a piece containing a non-interval"
        in
        let i_list = List.map get_piece v_list in
        Piece (sort_pc (make_piece i_list))
    and eval_squeeze v = 
        match v with
        | Piece pc  -> Interval (squeeze_piece pc)
        | _         -> failwith (Printf.sprintf "Tried to squeeze %s. This is not a piece." (value_to_str v))

    (*match env with
    | stored_val :: env -> 
            (match var with
            | 0 -> stored_val
            | n -> eval_var tree (n-1))
    | [] -> failwith (Printf.sprintf "Variable \"%i\" not bound in tree!" var) *)

    and eval_divide (i, r) =
        match (i, r) with
        | (Interval i, Point pt) -> 
                let (i_l, i_r) = divide i pt in
                Tup [Interval i_l; Interval i_r]

        | _ -> failwith (Printf.sprintf "Tried to divide on incorrect arguments: (%S, %S)" (value_to_str i) (value_to_str r))

    and eval_ifthenelse(b, env, valns, e1, e2) =
        (match b with
        | Bool true -> eval env e1 valns
        | Bool false -> eval env e2 valns
        | _ -> failwith "Not boolean!")

    and eval_eval(n, i, valns) =
        let evals = List.map (fun valn -> valn.eval) valns in
        (match (n, i) with
        | (Num n, Interval i) ->
                let v = val_lift (List.nth evals n) in 
                Real (v (i))

        | (Num n, Piece pc) ->
                let v = val_lift (List.nth evals n) in 
                Real (v (squeeze_piece pc))
        | _ -> failwith (Printf.sprintf "Eval expects Num and Piece. Received %s and %s" (value_to_str n) (value_to_str i)))

    and eval_mark(n, i, a, valns) =
        let evals = List.map (fun valn -> valn.eval) valns in
        let marks = List.map (fun valn -> valn.mark) valns in
        (match (n, i, a) with
        | (Num n, Interval i, Real a) ->
            if real_geq a (0, None) then
            if real_geq (1, None) a then
                let m = mark_lift (List.nth evals n) (List.nth marks n) in
                Point (m i a)
            else failwith "Value to attain is larger than 1!"
            else failwith "Value to attain is smaller than 0!"
        | _ -> failwith (Printf.sprintf "Mark expects Num, Interval and Real. Received %s, %s, and %s" (value_to_str n) (value_to_str i) (value_to_str a)))
    
    and eval_markw(n, i, a, valns) = 
        let evals = List.map (fun valn -> valn.eval) valns in
        let marks = List.map (fun valn -> valn.mark) valns in
        (match (n, i, a) with
        | (Num n, Interval i, Real a) ->
            if real_geq a (0, None) then
            if real_geq (1, None) a then
                let v = val_lift (List.nth evals n) in
                let m = mark_lift (List.nth evals n) (List.nth marks n) in
                let a = a *. (v i) in
                Point (m i a)
            else failwith "Value to attain is larger than 1!"
            else failwith "Value to attain is smaller than 0!"
        | _ -> failwith (Printf.sprintf "MarkW expects Num, Interval and Real. Received %s, %s, and %s" (value_to_str n) (value_to_str i) (value_to_str a)))
