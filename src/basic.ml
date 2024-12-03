(* This is for basic things *)


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

let comp cop n1 n2 =
    match cop with
    | Geq -> (n1 >= n2)
    | Eq  -> (n1 = n2)

let cross_multiply r1 r2 = 
    match (r1, r2) with
    | ((n1, Some d1), (n2, Some d2))  -> (n1 * d2, n2 * d1)
    | ((n1, None), (n2, Some d2))     -> (n1 * d2, n2)
    | ((n1, Some d1), (n2, None))     -> (n1, n2 * d1)
    | ((n1, None), (n2, None))        -> (n1, n2)

let real_eq (r1 : real) (r2 : real) = 
    let (v1, v2) = cross_multiply r1 r2 in 
    comp Eq v1 v2 
    
let real_geq r1 r2 = 
    let (v1, v2) = cross_multiply r1 r2 in
    comp Geq v1 v2

let real_leq r1 r2 = real_geq r2 r1

let aop_num aop n1 n2 =
    match aop with
    | Plus -> n1 + n2
    | Times -> n1 * n2

let rec gcd a = function 
    | 0 -> a
    | b -> gcd b (a mod b)

(** [reduce r] returns a simplified version of the real number [r]. *)
let reduce ((n, d) : real) : real = 
    match d with 
    | None -> (n, None)
    | Some d -> let x = gcd n d in (n / x, Some (d / x))

let aop_real aop r1 r2 = 
    let ((n1, d1), (n2, d2)) = (r1, r2) in
    match aop with
    | Plus -> 
            (match (d1, d2) with
            | (Some d1, Some d2)    -> ((d2 * n1) + (d1 * n2), Some (d1 * d2))
                |> reduce
            | (Some d1, None)       -> (n1 + (d1 * n2), Some d1)   |> reduce
            | (None, Some d2)       -> ((n1 * d2) + n2, Some d2)   |> reduce
            | (None, None)          -> (n1 + n2, None))            |> reduce 
    | Times ->
            (match (d1, d2) with
            | (Some d1, Some d2)    -> ((n1 * n2), Some (d1 * d2)) |> reduce 
            | (Some d1, None)       -> ((n1 * n2), Some d1)        |> reduce 
            | (None, Some d2)       -> ((n1 * n2), Some d2)        |> reduce 
            | (None, None)          -> (n1 * n2, None))            |> reduce 

let aop_real_list aop l =
    let null = match aop with | Plus -> (0, None) | Times -> (1, None) in
    let rec helper acc l =
        match l with
        | r :: [] -> r
        | r :: t -> helper (aop_real aop acc r) t
        | [] -> acc
    in helper null l

let negate r = 
    match r with
    | (d, None)    -> (-d, None)
    | (d, Some n)  -> (-d, Some n)

let minus r1 r2 = aop_real Plus r1 (negate r2)

type interval = {l : real; r : real}

let geq = real_geq
let leq r r' = geq r' r
let plus = aop_real Plus
let (+.) a b = plus a b
let (>=) a b = geq a b
let (<=) a b = leq a b
let (-.) a b = minus a b

let bop_bool bop b1 b2 = 
    match bop with
    | And -> b1 && b2
    | Or  -> b1 || b2

type piece = {lvl : level; pc : interval list}
and level =
    | Cake
    | Sq of piece

type vinterval = {lvl : level; i : interval}
type point = {lvl : level; pt : real}

    (* Ordering and sorting intervals and pieces *)
    (* We assume that all intervals are disjoint *)
let i_leq i1 i2 = leq i1.r i2.l

let comp_i i1 i2 = 
    if i1 = i2 then 0 else
    if i_leq i1 i2 then -1 else 1

    (* Sorts the physical piece *)
let sort_piece pc = (List.sort comp_i pc)

(* Sorts the piece that has extra stuff *)
let sort_pc (pc : piece) = {lvl = pc.lvl; pc = sort_piece pc.pc}



let piece_length pc = 
    let i_length_sum = 
    fun acc i -> acc +. (i.r -. i.l) 
    in
    List.fold_left i_length_sum (0, None) pc.pc

type pt_containment =
    | Left
    | Right
    | Inside

    (* Cont is short for containment. 
       Left means that the point is to the left of the interval.
       Right means that the point is to the right of the interval.
       Inside means it is inside the interval, but not equal to the endpoints.
       *)
let cont (pt : real) (i : interval) = 
    if pt <= i.l then 
        Left
    else
        if pt <= i.r then
            Inside
        else 
            Right

    (* This assumes that there is some overlap between the piece pc and interval i*)
let intersect (i : interval) (pc : interval list) =
    let rec right_part acc pc =
        match pc with
        | i' :: p' -> 
                begin match cont i.r i' with
                | Left      -> acc
                | Inside    -> acc @ [{l = i'.l; r = i.r}]
                | Right     -> right_part (acc @ [i'])  p'
                end
        | []        -> acc
    in
    let rec left_part pc =
        match pc with
        | i' :: p' -> 
                begin match cont i.l i' with
                | Left      -> 
                        begin match cont i.r i' with
                        | Left   -> failwith "No overlap"
                        | Inside -> [{l = i'.l;r = i.r}]
                        | Right  -> right_part [i'] p'
                        end
                | Inside    -> 
                        begin match cont i.r i' with
                        | Left   -> failwith "cannot happen"
                        | Inside -> [{l = i.l;r = i.r}]
                        | Right  -> right_part [{l = i.l;r = i'.r}] p'
                        end
                | Right     -> left_part p'
                end
        | []        -> failwith "No overlap"
    in
    left_part pc


let rec len p =
    match p with
    | i :: p'   -> (i.r -. i.l) +. (len p')
    | []        -> (0, None)

let contains_base (pc : interval list) (pt : real) = 
    List.fold_left (fun acc i -> acc || (i.r >= pt) && (pt >= i.l)) false pc

let contains (pc : piece) (pt : point) =
    assert (pc.lvl = pt.lvl);
    (contains_base pc.pc pt.pt)

let squeeze_piece (pc : piece) = {lvl = Sq pc; i = {l = (0, None); r = (len pc.pc)}}

       

(* Takes a point down a level *)
let unsqueeze_pt (pt : point) : point =
    match pt.lvl with
    | Cake  -> pt
    | Sq pc -> 
        assert ((len pc.pc) >= pt.pt);
        let rec h pc pt =
            match pc with
            | i :: pc' -> 
                    let len = len [i] in
                    if len >= pt then
                        pt +. i.l
                    else 
                        h pc' (pt -. len)
            | _         -> failwith "Cannot happen"
        in {lvl = pc.lvl; pt = (h pc.pc pt.pt)}


let unsqueeze_i (i : vinterval) =
    match i.lvl with
    | Cake -> {lvl = Cake; pc = [i.i]}
    | Sq pc -> 
        let l, r = {lvl = i.lvl; pt = i.i.l}, {lvl = i.lvl; pt = i.i.r} in
        let l, r = unsqueeze_pt l, unsqueeze_pt r in
        {lvl = pc.lvl; pc = (intersect {l = l.pt; r = r.pt} pc.pc)}

(* takes in a point and converts it to a point of that kind of piece *)
let new_point (pc : piece) (pt : point) =
    assert (contains pc pt);
    let pc_rev = List.rev pc.pc in
    let rec h pc = 
        match pc with
        | i' :: pc'  -> 
                if contains_base [i'] pt.pt then
                    (len pc') +. (pt.pt -. i'.l)
                else
                    h pc'
        | []        -> failwith "Cannot happen since pc contains pt"
    in {lvl = Sq pc; pt = (h pc_rev)}



let make_piece (i_list : vinterval list) = 
    let rec h lvl (i_list : vinterval list) =
        match i_list with
        | i :: i_list' -> 
                    if i.lvl = lvl then 
                        if real_eq i.i.l i.i.r then
                            h lvl i_list'
                        else
                            i.i :: (h lvl i_list') 
                    else failwith "Cannot form a piece of this list of intervals!"
        | []           -> []
    in
    match i_list with
    | i :: i_list'  -> 
            let rest = (h i.lvl i_list') in
            let pc = if real_eq i.i.l i.i.r then 
                rest
            else
                i.i :: rest
            in
            {lvl = i.lvl; pc = pc}
    | []            -> {lvl = Cake; pc = []}



let divide (i : vinterval) (pt : point) = 
    assert (i.lvl = pt.lvl);
    assert (i.i.r >= pt.pt);
    assert (pt.pt >= i.i.l);
    let i_l, i_r  = {lvl = i.lvl ; i = {l = i.i.l; r = pt.pt}}, {lvl = i.lvl; i = {l = pt.pt; r = i.i.r}} in
    (i_l, i_r)


(* Agent preference implementation *)
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

let rec val_eq v1 v2 = 
    match v1, v2 with
    | Real r1, Real r2 -> (r1 = r2)
    | Num n1, Num n2 -> (n1 = n2)
    | Bool b1, Bool b2 -> (b1 = b2)
    | Point pt1, Point pt2 -> (pt1 = pt2)
    | Interval i1, Interval i2 -> (i1 = i2)
    | Piece pc1, Piece pc2 -> (pc1 = pc2)
    | Tup vl1, Tup vl2 -> 
            begin
            try 
                List.fold_left (fun b (v1, v2) -> b && (val_eq v1 v2)) true (List.combine vl1 vl2)
            with (Invalid_argument _) -> false
            end
    | _         -> failwith "Cannot equate two distinct kinds of values"


let apply_op op v_list =
    match op, v_list with
    | A aop, [v1; v2] -> 
            begin match v1, v2 with
            | Real r1, Real r2 -> Real (aop_real aop r1 r2)
            | Num n1, Num n2 -> Num (aop_num aop n1 n2)
            | _  -> failwith "Cannot apply specified op to specified values."
            end
    | B bop, [Bool b1; Bool b2] -> Bool (bop_bool bop b1 b2)
    | C cop, [v1; v2] -> 
            begin match cop, v1, v2 with
            | Geq, Real r1, Real r2 -> Bool (real_geq r1 r2)
            | Geq, Point pt1, Point pt2 ->
                    begin if pt1.lvl != pt2.lvl then
                        failwith "Attempting to compare points from different levels"
                    else
                        Bool (real_geq pt1.pt pt2.pt)
                    end
            | Eq, v1, v2 -> Bool (val_eq v1 v2)
            | _ -> failwith "Cannot apply comparison operator to these arguments"
            end
    | Not, [Bool b]        -> Bool (not b)
    | Neg, [Real r]        -> Real (negate r)
    | _ -> failwith "Cannot apply specified op to specified values."


let p = Printf.sprintf

let real_to_str r =
    match r with
    | (n, Some d)   -> p "%i/%i" n d
    | (n, None)     -> p "%i" n
    
let rec interval_list_to_str pc =
    match pc with
    | i :: []   -> p "[%s, %s]" (real_to_str i.l) (real_to_str i.r)
    | i :: pc'  -> p "[%s, %s], %s" (real_to_str i.l) (real_to_str i.r) (interval_list_to_str pc')
    | []        -> ""


let rec piece_to_str (pc : piece) = 
    (lvl_to_str pc.lvl) ^ (interval_list_to_str pc.pc)
and lvl_to_str lvl =
    match lvl with
    | Cake -> ""
    | Sq pc -> p "{%s} " (piece_to_str pc)

let vinterval_to_str i = 
    let s = p "[%s, %s]" (real_to_str i.i.l) (real_to_str i.i.r) in
    (lvl_to_str i.lvl) ^ s

let point_to_str pt =
    (lvl_to_str pt.lvl) ^ (real_to_str pt.pt)

let aop_to_str (op : aop) =
    match op with
    | Plus -> "+"
    | Times -> "*"

let bop_to_str (bop : bop) =
    match bop with
    | And -> "∧"
    | Or -> "∨"

let cop_to_str (op : cop) =
    match op with
    | Geq -> "≥"
    | Eq -> "="

let rec value_to_str v = 
    match v with
    | Real r     -> real_to_str r
    | Num n      -> (string_of_int n)
    | Bool b     -> (string_of_bool b)
    | Tup v_list -> "(" ^ tup_to_str v_list 
    | Point pt   -> point_to_str pt
    | Interval i -> vinterval_to_str i
    | Piece pc   -> piece_to_str pc
and tup_to_str v_list =
    match v_list with
    | v :: []      -> value_to_str v ^ ")" 
    | v :: v_list' -> value_to_str v ^ ", " ^ tup_to_str v_list'
    | []           -> ""
 
let string_list sl = 
    let rec helper sl = 
        match sl with
        | h :: [] -> p "%s]" h
        | h :: t -> p "%s, %s" h (helper t)
        | [] -> ""
    in p "[%s" (helper sl)

let op_as_str op =
    match op with
    | A aop -> aop_to_str aop
    | B bop -> bop_to_str bop
    | C cop -> cop_to_str cop
    | Not   -> "not"
    | Neg   -> "-"

let op_to_str op arguments =
    match op, arguments with
    | A aop, [s1; s2] -> p "%s %s %s" s1 (aop_to_str aop) s2
    | B bop, [s1; s2] -> p "%s %s %s" s1 (bop_to_str bop) s2
    | C cop, [s1; s2] -> p "%s %s %s" s1 (cop_to_str cop) s2
    | Not, [s]        -> p "not %s" s 
    | Neg, [s]        -> p "-%s" s
    | A aop, l -> p "(%s) %s" (aop_to_str aop) (string_list l)
    | B bop, l -> p "(%s) %s" (bop_to_str bop) (string_list l) 
    | C cop, l -> p "(%s) %s" (cop_to_str cop) (string_list l)
    | Not, l -> p "(not) %s" (string_list l)
    | Neg, l -> p "(-) %s" (string_list l)
 


open Format 
let kwd = pp_print_string
let num = pp_print_int

let real_formatter f r = kwd f (real_to_str r)
let interval_formatter f i = kwd f "["; real_formatter f i.l; kwd f ","; real_formatter f i.r; kwd f "]"
let rec piece_formatter f (pc : piece) = 
    let rec h l =
        match l with
        | i :: [] -> interval_formatter f i
        | i :: l' -> interval_formatter f i; kwd f ";"; h l'
        | []      -> ()
    in
    lvl_formatter f pc.lvl ; pp_print_cut f (); pp_open_hbox f (); h pc.pc; close_box ()
and lvl_formatter f lvl =
    match lvl with
    | Cake -> ()
    | Sq pc -> kwd f "{" ; piece_formatter f pc ; kwd f "} "
let vinterval_formatter f (i : vinterval) =
    lvl_formatter f i.lvl ; interval_formatter f i.i
let point_formatter f pt = 
    lvl_formatter f pt.lvl ; real_formatter f pt.pt

let rec value_formatter f v = 
    match v with
    | Real r     -> real_formatter f r
    | Num n      -> num f n 
    | Bool b     -> if b then kwd f "true" else kwd f "false"
    | Point pt   -> point_formatter f pt
    | Interval i -> vinterval_formatter f i
    | Piece pc   -> piece_formatter f pc
    | Tup v_list -> kwd f "(" ; pp_open_hbox f (); tup_fmt f v_list ; close_box (); kwd f ")"
and tup_fmt f v_list  =
    match v_list with
    | v :: []      -> value_formatter f v 
    | v :: v_list' -> value_formatter f v; kwd f ", "; tup_fmt f v_list'
    | []           -> ()
 
 

