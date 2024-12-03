open Basic
open Ast
open Path

(* utyp is all the usual types + read only types*)
type utyp = Bool | Num | Real | Val | Point | RInterval | RPiece

(* ltyp are the "linear" types*)
and ltyp = Interval | Piece | Tup of typ list
and typ = Lin of ltyp | Un of utyp

let rec ltyp_to_read ltyp =
  match ltyp with
  | Interval -> Un RInterval
  | Piece -> Un RPiece
  | Tup t_list ->
      Lin
        (Tup
           (List.map
              (fun t -> match t with Lin t -> ltyp_to_read t | Un t -> Un t)
              t_list))

let is_linear typ = match typ with Lin _ -> true | Un _ -> false
let concatspec s1 s2 = s1 ^ " * " ^ s2

let rec typ_to_str (t : typ) =
  match t with Lin t -> ltyp_to_str t | Un t -> utyp_to_str t

and ltyp_to_str t =
  match t with
  | Interval -> "Interval"
  | Piece -> "Piece"
  | Tup t_list -> (
      match List.map typ_to_str t_list with
      | h :: t -> List.fold_left concatspec h t
      | [] -> failwith "type of empty tup")

and utyp_to_str t =
  match t with
  | Bool -> "Bool"
  | Num -> "Num"
  | Real -> "Real"
  | Point -> "Point"
  | Val -> "Val"
  | RInterval -> "RInterval"
  | RPiece -> "RPiece"

let list_to_str l =
  let p = Printf.sprintf in
  let rec helper l =
    match l with
    | h :: [] -> p "%s]" h
    | h :: t -> p "%s; %s" h (helper t)
    | [] -> ""
  in
  p "[%s" (helper l)

let typ_to_utyp t =
  match t with
  | Un t -> t
  | Lin t ->
      failwith
        (Printf.sprintf "Cannot make %s an unrestricted type" (ltyp_to_str t))

type sgn = { args : utyp list; ret : utyp }

let or_str l =
  let p = Printf.sprintf in
  let rec helper l =
    match l with
    | h :: [] -> p "or %s" h
    | h :: t -> p "%s, %s" h (helper t)
    | [] -> ""
  in
  helper l

exception Variable_missassignment of string
exception Variable_overuse of string

let raise_var_overuse var_list =
  let var_list_string = list_to_str ((List.map var_string) var_list) in
  let msg =
    Printf.sprintf "Variables %s have linear types yet are used more than once."
      var_list_string
  in
  raise (Variable_overuse msg)

exception Incorrect_signature of string

let raise_inc_sgn op (expected : utyp list list) (received : utyp list) =
  let t_strs =
    List.map (fun t_list -> list_to_str (List.map utyp_to_str t_list)) expected
  in
  let s1 = or_str t_strs in
  let s2 = list_to_str (List.map utyp_to_str received) in
  let msg =
    Printf.sprintf
      "Operator %s exptected types %s as arguments but received types %s"
      (op_as_str op) s1 s2
  in
  raise (Incorrect_signature msg)

let eq_msg tlist =
  let p = Printf.sprintf in
  let rcv_str = list_to_str (List.map utyp_to_str tlist) in
  p "Op (=) expects two arguments of the same type but received types %s."
    rcv_str

(* Gives the possible signatures of given operations *)
let sgn op =
  let get_types (exp_types : utyp list list) input =
    match List.find_opt (fun tl -> tl = input) exp_types with
    | Some _ -> ()
    | None -> raise_inc_sgn op exp_types input
  in
  match op with
  | A Plus ->
      let exp_types : utyp list list =
        [ [ Real; Real ]; [ Num; Num ]; [ Val; Val ] ]
      in
      fun tlist ->
        get_types exp_types tlist;
        { args = tlist; ret = List.hd tlist }
  | A Times ->
      let exp_types : utyp list list =
        [ [ Real; Real ]; [ Real; Val ]; [ Val; Real ]; [ Num; Num ] ]
      in
      fun tlist ->
        get_types exp_types tlist;
        let ret =
          if tlist = [ Real; Val ] || tlist = [ Val; Real ] then Val
          else List.hd tlist
        in
        { args = tlist; ret }
  | B _ ->
      let exp_types : utyp list list = [ [ Bool; Bool ] ] in
      fun tlist ->
        get_types exp_types tlist;
        { args = tlist; ret = Bool }
  | C cop -> (
      match cop with
      | Eq -> (
          fun tlist ->
            match tlist with
            | [ t1; t2 ] ->
                if t1 = t2 then { args = tlist; ret = Bool }
                else raise (Incorrect_signature (eq_msg tlist))
            | _ -> raise (Incorrect_signature (eq_msg tlist)))
      | Geq ->
          let exp_types = [ [ Real; Real ]; [ Val; Val ]; [ Point; Point ] ] in
          fun tlist ->
            get_types exp_types tlist;
            { args = tlist; ret = Bool })
  | Not ->
      let exp_types = [ [ Bool ] ] in
      fun tlist ->
        get_types exp_types tlist;
        { args = [ Bool ]; ret = Bool }
  | Neg ->
      let exp_types = [ [ Num ]; [ Real ] ] in
      fun tlist ->
        get_types exp_types tlist;
        { args = tlist; ret = List.hd tlist }

let rec type_of_value (v : value) =
  match v with
  | Real _ -> Un Real
  | Num _ -> Un Num
  | Bool _ -> Un Bool
  | Point _ -> Un Point
  | Interval _ -> Lin Interval
  | Piece _ -> Lin Piece
  | Tup vlist -> Lin (Tup ((List.map type_of_value) vlist))

type environment = (int list * typ) list

exception Var_not_unique of string

(* This type is for keeping track of how many times a variable has been mentioned. Lin means it occured exactly once. Aff means it occurs at most once. Un is everything else *)
type occ = Lin | Aff | Un

let comb occ occ' =
  match (occ, occ') with
  | Some Lin, None -> Some Lin
  | None, Some Lin -> Some Lin
  | Some Aff, None -> Some Aff
  | None, Some Aff -> Some Aff
  | None, None -> None
  | _ -> Some Un

let combif occ occ' =
  match (occ, occ') with
  | None, None -> None
  | Some Lin, None -> Some Aff
  | None, Some Lin -> Some Aff
  | Some Lin, Some Lin -> Some Lin
  | Some Un, _ -> Some Un
  | _, Some Un -> Some Un
  | _ -> Some Aff

let comb_unit var_list = List.map (fun _ -> None) var_list

let merge_tallies tlist =
  match tlist with
  | t :: tlist' -> List.fold_left (fun t1 t2 -> List.map2 comb t1 t2) t tlist'
  | [] -> []

let merge_branch_tallies t1 t2 = List.map2 combif t1 t2

let rec contains l x =
  match l with y :: l' -> if y = x then true else contains l' x | [] -> false

(* This keeps track of the usage of variables within the expression *)
let rec var_usage var_list (e : expression) =
  let h = var_usage var_list in
  match e with
  | Val _ -> List.map (fun _ -> None) var_list
  | Op (_, e_list) -> merge_tallies (List.map h e_list)
  | Var x ->
      let f =
        if is_read x then fun _ -> None
        else fun y -> if y = var_id x then Some Lin else None
      in
      List.map f var_list
  | Divide (e1, e2) -> merge_tallies [ h e1; h e2 ]
  | Let (l, e1, e2) ->
      let t2 =
        List.map2
          (fun x occ -> if contains l x then None else occ)
          var_list (h e2)
      in
      merge_tallies [ h e1; t2 ]
  | IfThenElse (e1, e2, e3) ->
      merge_tallies [ h e1; merge_branch_tallies (h e2) (h e3) ]
  | Tuple e_list -> merge_tallies (List.map h e_list)
  | Piece e_list -> merge_tallies (List.map h e_list)
  | Mark (e1, e2, e3) -> merge_tallies [ h e1; h e2; h e3 ]
  | MarkW (e1, e2, e3) -> merge_tallies [ h e1; h e2; h e3 ]
  | Eval (e1, e2) -> merge_tallies [ h e1; h e2 ]
  | Squeeze e -> h e
  | Cake -> []
  | Union (e1, e2) -> merge_tallies [ h e1; h e2 ]

let assign_vars_types var_list (typ : typ) =
  match (var_list, typ) with
  | var_list, Lin (Tup t_list) -> List.combine var_list t_list
  | [ x ], typ -> [ (x, typ) ]
  | _ ->
      let str = list_to_str (List.map var_string var_list) in
      let tstr = typ_to_str typ in
      let msg =
        Printf.sprintf "Cannot assign type %s to variables %s." str tstr
      in
      raise (Variable_missassignment msg)

let rec typ_of_exp (env : environment) (e : expression) =
  match e with
  | Val v -> type_of_value v
  | Var x -> typ_var env x
  | Divide (e1, e2) -> typ_divide env e1 e2
  | Let (l, e1, e2) -> typ_let env l e1 e2
  | Op (op, e_list) -> typ_op env op e_list
  | IfThenElse (e1, e2, e3) -> typ_ifthenelse env e1 e2 e3
  | Tuple e_list -> Lin (Tup (List.map (typ_of_exp env) e_list))
  | Mark (e0, e1, e2) -> typ_mark env e0 e1 e2
  | MarkW (e0, e1, e2) -> typ_markw env e0 e1 e2
  | Eval (e0, e) -> typ_eval env e0 e
  | Cake -> Lin Interval
  | Piece e_list -> typ_piece env e_list
  | Union (e1, e2) -> typ_union env e1 e2
  | Squeeze e -> typ_squeeze env e

and typ_var env x =
  match x with
  | N l -> List.assoc l env
  | Read l -> (
      match List.assoc l env with
      | Lin ltyp -> ltyp_to_read ltyp
      | Un ut ->
          failwith
            (p "Cannot assign read variable to non-linear type %s."
               (typ_to_str (Un ut))))

and typ_union env e1 e2 =
  match (typ_of_exp env e1, typ_of_exp env e2) with
  | Lin Piece, Lin Piece -> Lin Piece
  | _ -> failwith "Tried to unite two non-pieces!"

and typ_piece env e_list =
  let t_list = List.map (typ_of_exp env) e_list in
  let wrong =
    List.filter_map
      (fun (typ : typ) -> if typ = Lin Interval then None else Some typ)
      t_list
  in
  match wrong with
  | [] -> Lin Piece
  | _ -> failwith "Tried to construct a piece using non-intervals!"

and typ_divide env e1 e2 =
  match (typ_of_exp env e1, typ_of_exp env e2) with
  | Lin Interval, Un Point -> Lin (Tup [ Lin Interval; Lin Interval ])
  | t1, t2 ->
      failwith
        (p "Divide expects types Interval and Point. Received types %s and %s. "
           (typ_to_str t1) (typ_to_str t2))

and typ_let env var_list e1 e2 =
  let t = typ_of_exp env e1 in
  let vars_types = assign_vars_types var_list t in
  let lin_vars_and_type =
    List.filter (fun (_, typ) -> is_linear typ) vars_types
  in
  let lin_vars, _ = List.split lin_vars_and_type in
  let lin_var_usage = List.combine lin_vars (var_usage lin_vars e2) in
  let too_many_occurrences =
    List.filter (fun (_, occ) -> occ = Some Un) lin_var_usage
  in
  if too_many_occurrences != [] then
    let bad_vars, _ = List.split too_many_occurrences in
    raise_var_overuse bad_vars
  else typ_of_exp (vars_types @ env) e2

and typ_ifthenelse env e1 e2 e3 =
  let t1, t2, t3 = (typ_of_exp env e1, typ_of_exp env e2, typ_of_exp env e3) in
  if t1 = Un Bool then
    if t2 = t3 then t2
    else
      failwith
        (p "IfThenElse expects the same types. Received types %s and %s."
           (typ_to_str t2) (typ_to_str t3))
  else
    failwith
      (p "IfThenElse expects type bool. Received type %s." (typ_to_str t1))

and typ_mark env e0 e1 e2 =
  match (typ_of_exp env e0, typ_of_exp env e1, typ_of_exp env e2) with
  | Un Num, Un RInterval, Un Val -> Un Point
  | t0, t1, t2 ->
      failwith
        (p
           "Mark expects types Num, Interval, and Real. Received %s, %s, and \
            %s."
           (typ_to_str t0) (typ_to_str t1) (typ_to_str t2))

and typ_markw env e0 e1 e2 =
  match (typ_of_exp env e0, typ_of_exp env e1, typ_of_exp env e2) with
  | Un Num, Un RInterval, Un Real -> Un Point
  | t0, t1, t2 ->
      failwith
        (p
           "MarkW expects types Num, Interval and Real. Received %s, %s, and \
            %s."
           (typ_to_str t0) (typ_to_str t1) (typ_to_str t2))

and typ_eval env e0 e =
  match (typ_of_exp env e0, typ_of_exp env e) with
  | Un Num, Un RPiece -> Un Val
  | Un Num, Un RInterval -> Un Val
  | t0, t ->
      failwith
        (p
           "Eval expects types Num and RPiece or Num and RInterval. Received \
            %s and %s."
           (typ_to_str t0) (typ_to_str t))

and typ_op env op e_list =
  let tlist =
    List.map (fun typ -> typ |> typ_of_exp env |> typ_to_utyp) e_list
  in
  Un ((sgn op) tlist).ret

and typ_squeeze env e =
  match typ_of_exp env e with
  | Lin Piece -> Lin Interval
  | typ ->
      failwith (p "Squeeze expects Piece input. Received %s." (typ_to_str typ))

let type_error_msg info = msg_from_info info

exception Type_error of string

let raise_var_overuse_pre_exp var_list =
  let var_list_string = list_to_str var_list in
  let msg =
    Printf.sprintf
      "Variable(s) %s have linear types yet are used more than once."
      var_list_string
  in
  raise (Variable_overuse msg)

let rec type_list_to_str t_list =
  match t_list with
  | typ :: [] -> p "and %s" (typ_to_str typ)
  | typ :: t_list' -> p "%s, %s" (typ_to_str typ) (type_list_to_str t_list')
  | [] -> ""

let merge_tallies tlist =
  match tlist with
  | t :: tlist' -> List.fold_left (fun t1 t2 -> List.map2 comb t1 t2) t tlist'
  | [] -> []

let merge_branch_tallies t1 t2 = List.map2 combif t1 t2

let rec var_usage var_list (dl : definition list) abbrv_env (e : pre_expression)
    =
  let h = var_usage var_list dl abbrv_env in
  match e with
  | _, Val _ -> List.map (fun _ -> None) var_list
  | _, Op (_, e_list) -> merge_tallies (List.map h e_list)
  | _, Var x -> (
      if is_read_pre x then List.map (fun _ -> None) var_list
      else
        match List.assoc_opt (pre_var_id x) abbrv_env with
        | Some var_usage -> var_usage
        | None ->
            List.map
              (fun y -> if y = pre_var_id x then Some Lin else None)
              var_list)
  | info, Abbreviation (name, args) ->
      var_abbrv_usage var_list dl abbrv_env name args info
  | _, Divide (e1, e2) -> merge_tallies [ h e1; h e2 ]
  | _, Let (l, e1, e2) ->
      (* Need to remove variables from abbreviation environment if they are bound by this let binding to properly handle shadowing *)
      let abbrv_env' =
        List.filter (fun (x, _) -> not (pattern_contains x (List l))) abbrv_env
      in
      let var_usage_e2 = var_usage var_list dl abbrv_env' e2 in
      let t2 =
        List.map2
          (fun x occ -> if pattern_contains x (List l) then None else occ)
          var_list var_usage_e2
      in
      merge_tallies [ h e1; t2 ]
  | _, IfThenElse (e1, e2, e3) ->
      merge_tallies [ h e1; merge_branch_tallies (h e2) (h e3) ]
  | _, Tuple e_list -> merge_tallies (List.map h e_list)
  | _, Piece e_list -> merge_tallies (List.map h e_list)
  | _, Mark (e1, e2, e3) -> merge_tallies [ h e1; h e2; h e3 ]
  | _, MarkW (e1, e2, e3) -> merge_tallies [ h e1; h e2; h e3 ]
  | _, Eval (e1, e2) -> merge_tallies [ h e1; h e2 ]
  | _, Squeeze e -> h e
  | _, Cake -> []
  | _, Union (e1, e2) -> merge_tallies [ h e1; h e2 ]

and var_abbrv_usage var_list dl abbrv_env name args info =
  let arg_usage = List.map (var_usage var_list dl abbrv_env) args in
  let df, rest = get_defn dl name info in
  let df_env =
    try List.combine df.args arg_usage
    with _ ->
      failwith
        (p "%s. Cannot supply specified arguments to abbreviation %s."
           (type_error_msg info) df.name)
  in
  var_usage var_list rest df_env df.body

let rec pat_and_typs info (pat : pattern) (typ : typ) =
  match (pat, typ) with
  | List pats, Lin (Tup t_list) ->
      List.concat (List.map2 (pat_and_typs info) pats t_list)
  | List [ Var x ], typ -> pat_and_typs info (Var x) typ
  | Var x, typ -> [ (x, typ) ]
  | _ ->
      let pt_string = pat_to_str pat in
      let msg =
        Printf.sprintf "Pattern %s. %s" pt_string (msg_from_info info)
      in
      raise (Variable_missassignment msg)

let rec typ_of_pre_exp (dl : definition list) (env : (string * typ) list)
    (e : pre_expression) =
  let f = typ_of_pre_exp dl in
  match e with
  | _, Val v -> type_of_value v
  | info, Var x -> typ_var info env x
  | info, Op (op, e_list) -> typ_op info dl env op e_list
  | info, Abbreviation (s, e_list) ->
      let t_list = List.map (f env) e_list in
      let def, remaining = get_defn dl s info in
      let def_env =
        try List.combine def.args t_list
        with _ ->
          failwith
            (p "%s. Cannot supply specified arguments to abbreviation %s."
               (type_error_msg info) def.name)
      in
      typ_of_pre_exp remaining def_env def.body
  | info, Divide (e1, e2) -> typ_divide info dl env e1 e2
  | info, Let (var_list, e1, e2) -> typ_let info dl env var_list e1 e2
  | info, IfThenElse (e1, e2, e3) -> typ_ifthenelse info dl env e1 e2 e3
  | _, Tuple e_list -> Lin (Tup (List.map (typ_of_pre_exp dl env) e_list))
  | info, Mark (e0, e1, e2) -> typ_mark info dl env e0 e1 e2
  | info, MarkW (e0, e1, e2) -> typ_markw info dl env e0 e1 e2
  | info, Eval (e0, e) -> typ_eval info dl env e0 e
  | _, Cake -> Lin Interval
  | info, Piece e_list -> typ_piece info dl env e_list
  | info, Union (e1, e2) -> typ_union info dl env e1 e2
  | _, Squeeze _ -> Lin Interval

and typ_union info dl env e1 e2 =
  let typ1, typ2 = (typ_of_pre_exp dl env e1, typ_of_pre_exp dl env e2) in
  match (typ1, typ2) with
  | Lin Piece, Lin Piece -> Lin Piece
  | _ ->
      raise
        (Type_error
           (p "%s. Union expects types piece and piece. Received %s and %s."
              (type_error_msg info) (typ_to_str typ1) (typ_to_str typ2)))

and typ_piece info dl env e_list =
  let t_list = List.map (typ_of_pre_exp dl env) e_list in
  let wrong =
    List.filter_map
      (fun (typ : typ) -> if typ = Lin Interval then None else Some typ)
      t_list
  in
  match wrong with
  | [] -> Lin Piece
  | _ ->
      raise
        (Type_error
           (p "%s. Piece expects all types interval. Received types %s."
              (type_error_msg info) (type_list_to_str t_list)))

and typ_divide info dl env e1 e2 =
  match (typ_of_pre_exp dl env e1, typ_of_pre_exp dl env e2) with
  | Lin Interval, Un Point -> Lin (Tup [ Lin Interval; Lin Interval ])
  | t1, t2 ->
      raise
        (Type_error
           (p
              "%s. Divide expects types Interval and Point. Received types %s \
               and %s."
              (type_error_msg info) (typ_to_str t1) (typ_to_str t2)))

and typ_op info dl env op e_list =
  let tlist =
    List.map (fun e -> e |> typ_of_pre_exp dl env |> typ_to_utyp) e_list
  in
  try Un ((sgn op) tlist).ret
  with _ ->
    raise
      (Type_error
         (let tsl = list_to_str (List.map utyp_to_str tlist) in
          p "%s. Op %s received types %s." (op_as_str op) (type_error_msg info)
            tsl))

and typ_ifthenelse info dl env e1 e2 e3 =
  let t1, t2, t3 =
    ( typ_of_pre_exp dl env e1,
      typ_of_pre_exp dl env e2,
      typ_of_pre_exp dl env e3 )
  in
  if t1 = Un Bool then
    if t2 = t3 then t2
    else
      raise
        (Type_error
           (p "%s. IfThenElse expects the same types. Received types %s and %s."
              (type_error_msg info) (typ_to_str t2) (typ_to_str t3)))
  else
    raise
      (Type_error
         (p "%s. IfThenElse expects type bool. Received type %s."
            (type_error_msg info) (typ_to_str t1)))

and typ_mark info dl env e0 e1 e2 =
  match
    ( typ_of_pre_exp dl env e0,
      typ_of_pre_exp dl env e1,
      typ_of_pre_exp dl env e2 )
  with
  | Un Num, Un RInterval, Un Val -> Un Point
  | t0, t1, t2 ->
      raise
        (Type_error
           (p
              "%s. Mark expects types Num, Interval, and Real. Received types \
               %s, %s, and %s."
              (type_error_msg info) (typ_to_str t0) (typ_to_str t1)
              (typ_to_str t2)))

and typ_markw info dl env e0 e1 e2 =
  match
    ( typ_of_pre_exp dl env e0,
      typ_of_pre_exp dl env e1,
      typ_of_pre_exp dl env e2 )
  with
  | Un Num, Un RInterval, Un Real -> Un Point
  | t0, t1, t2 ->
      raise
        (Type_error
           (p
              "%s. Markw expects types Num, RInterval, and Real. Received \
               types %s, %s, and %s."
              (type_error_msg info) (typ_to_str t0) (typ_to_str t1)
              (typ_to_str t2)))

and typ_eval info dl env e0 e =
  match (typ_of_pre_exp dl env e0, typ_of_pre_exp dl env e) with
  | Un Num, Un RPiece -> Un Val
  | Un Num, Un RInterval -> Un Val
  | t0, t ->
      raise
        (Type_error
           (p
              "%s. Eval expects types Num and RPiece or Num and RInterval. \
               Received %s and %s."
              (type_error_msg info) (typ_to_str t0) (typ_to_str t)))

and typ_let info dl env p_list e1 e2 =
  let typ = typ_of_pre_exp dl env e1 in
  let new_vars_types = pat_and_typs info (List p_list) typ in
  let lin_vars_and_type =
    List.filter (fun (_, typ) -> is_linear typ) new_vars_types
  in
  let lin_vars, _ = List.split lin_vars_and_type in

  let lin_var_usage = List.combine lin_vars (var_usage lin_vars dl [] e2) in
  let too_many_occurrences =
    List.filter (fun (_, occ) -> occ = Some Un) lin_var_usage
  in
  if too_many_occurrences != [] then
    let bad_vars, _ = List.split too_many_occurrences in
    raise_var_overuse_pre_exp bad_vars
  else typ_of_pre_exp dl (new_vars_types @ env) e2

and typ_var info env x =
  match x with
  | N l -> List.assoc l env
  | Read l -> (
      match List.assoc l env with
      | Lin ltyp -> ltyp_to_read ltyp
      | Un ut ->
          failwith
            (p "%s. Cannot assign read variable to non-linear type %s."
               (type_error_msg info) (typ_to_str (Un ut))))

(* Types for paths do not check for the number of occurrences for each variable *)
let rec typ_of_path (env : (int list * typ) list) (e : path) =
  match e with
  | Val v -> type_of_value v
  | Var x -> typ_var env x
  | Divide (e1, e2) -> typ_divide env e1 e2
  | Let (l, e1, e2) -> typ_let env l e1 e2
  | Op (op, e_list) -> typ_op env op e_list
  | Assert (e1, e2) -> typ_assert env e1 e2
  | Tuple e_list -> Lin (Tup (List.map (typ_of_path env) e_list))
  | Mark (_, e1, e2) -> typ_mark env e1 e2
  | MarkW (_, e1, e2) -> typ_markw env e1 e2
  | Eval (_, e) -> typ_eval env e
  | Piece e_list -> typ_piece env e_list
  | Squeeze e -> typ_squeeze env e
  | Cake -> Lin Interval
  | Union (e1, e2) -> typ_union env e1 e2

and typ_var env x =
  match x with
  | N l -> List.assoc l env
  | Read l -> (
      match List.assoc l env with
      | Lin ltyp -> ltyp_to_read ltyp
      | Un ut ->
          failwith
            (p "Cannot assign read variable to non-linear type %s."
               (typ_to_str (Un ut))))

and typ_op env op e_list =
  let tlist =
    List.map (fun typ -> typ |> typ_of_path env |> typ_to_utyp) e_list
  in
  Un ((sgn op) tlist).ret

and typ_union env e1 e2 =
  match (typ_of_path env e1, typ_of_path env e2) with
  | Lin Piece, Lin Piece -> Lin Piece
  | _ -> failwith "Tried to unite two non-pieces!"

and typ_piece env e_list =
  let t_list = List.map (typ_of_path env) e_list in
  let wrong =
    List.filter_map
      (fun (typ : typ) -> if typ = Lin Interval then None else Some typ)
      t_list
  in
  match wrong with
  | [] -> Lin Piece
  | _ -> failwith "Tried to construct a piece using non-intervals!"

and typ_squeeze env e =
  let t = typ_of_path env e in
  if t = Lin Piece then Lin Interval
  else failwith (p "Squeeze expects piece. Received %s." (typ_to_str t))

and typ_divide env e1 e2 =
  match (typ_of_path env e1, typ_of_path env e2) with
  | Lin Interval, Un Point -> Lin (Tup [ Lin Interval; Lin Interval ])
  | t1, t2 ->
      failwith
        (p "Divide expects types Interval and Point. Received types %s and %s. "
           (typ_to_str t1) (typ_to_str t2))

and typ_let env var_list e1 e2 =
  match typ_of_path env e1 with
  | Lin (Tup t_list) ->
      let env' = List.combine var_list t_list @ env in
      typ_of_path env' e2
  | t -> (
      match var_list with
      | [ x ] -> typ_of_path ((x, t) :: env) e2
      | _ -> raise (Variable_missassignment ""))

and typ_assert env e1 e2 =
  let t1, t2 = (typ_of_path env e1, typ_of_path env e2) in
  if t1 = Un Bool then t2
  else
    failwith (p "Assert expects type bool. Received type %s." (typ_to_str t1))

and typ_mark env e1 e2 =
  match (typ_of_path env e1, typ_of_path env e2) with
  | Un RInterval, Un Val -> Un Point
  | t1, t2 ->
      failwith
        (p "Mark expects types Interval and Real. Received %s, and %s."
           (typ_to_str t1) (typ_to_str t2))

and typ_markw env e1 e2 =
  match (typ_of_path env e1, typ_of_path env e2) with
  | Un RInterval, Un Real -> Un Point
  | t1, t2 ->
      failwith
        (p "MarkW expects types Interval and Real. Received %s, and %s."
           (typ_to_str t1) (typ_to_str t2))

and typ_eval env e =
  match typ_of_path env e with
  | Un RPiece -> Un Val
  | Un RInterval -> Un Val
  | t -> failwith (p "Eval expects type piece. Received %s." (typ_to_str t))
