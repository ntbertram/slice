open Basic
open List

type variable = N of int list | Read of int list
type binding_variable = int list

let is_read x = match x with N _ -> false | Read _ -> true

type expression =
  | Val of value
  | Op of op * expression list
  | Var of variable
  | Let of binding_variable list * expression * expression
  | IfThenElse of expression * expression * expression
  | Tuple of expression list
  | Cake
  | Divide of expression * expression
  | Mark of expression * expression * expression
  | MarkW of expression * expression * expression
  | Eval of expression * expression
  | Piece of expression list
  | Squeeze of expression
  | Union of expression * expression

(* Patterns for surface language *)
type pattern = Var of string | List of pattern list

let nvar l : expression = Var (N l)
let var_id x = match x with N l -> l | Read l -> l

(* Creates nested let bindings of patterns *)
let rec pattern_helper (env : (string * int list) list) (l : int list) plist e1
    =
  let vars = List.mapi (fun i _ -> i :: l) plist in
  let _, e', env =
    List.fold_left
      (fun acc p ->
        let i, containing_e, env = acc in
        match p with
        | Var x -> (i + 1, containing_e, (x, i :: l) :: env)
        | List pl ->
            let e1 : expression = nvar (i :: l) in
            let new_bindings, new_env = pattern_helper env (i :: l) pl e1 in
            (i + 1, (fun e -> containing_e (new_bindings e)), new_env))
      (0, (fun e -> e), env)
      plist
  in
  ((fun e2 -> Let (vars, e1, e' e2)), env)

type pre_info = {
  filename : string;
  start_lin : int;
  end_lin : int;
  start_col : int;
  end_col : int;
}

type 'a info = pre_info * 'a

let msg_from_info info =
  info.filename ^ " line(s) "
  ^ string_of_int info.start_lin
  ^ "-" ^ string_of_int info.end_lin ^ " col(s) "
  ^ string_of_int info.start_col
  ^ "-" ^ string_of_int info.end_col

type pre_var = N of string | Read of string

let pre_var_id x = match x with N str -> str | Read str -> str
let is_read_pre x = match x with N _ -> false | Read _ -> true

type pre_expression_no_info =
  | Val of value
  | Var of pre_var
  | Op of op * pre_expression list
  | Abbreviation of string * pre_expression list
  | Divide of pre_expression * pre_expression
  | Let of pattern list * pre_expression * pre_expression
  | IfThenElse of pre_expression * pre_expression * pre_expression
  | Tuple of pre_expression list
  | Mark of pre_expression * pre_expression * pre_expression
  | MarkW of pre_expression * pre_expression * pre_expression
  | Eval of pre_expression * pre_expression
  | Piece of pre_expression list
  | Squeeze of pre_expression
  | Cake
  | Union of pre_expression * pre_expression

(*re-define so info is outside of def, not inside*)
and pre_expression = pre_expression_no_info info

type definition = { name : string; args : string list; body : pre_expression }

let p = Printf.sprintf

let args_to_str args =
  let rec helper args =
    match args with
    | h :: [] -> p "%s)" h
    | h :: t -> p "%s, %s" h (helper t)
    | [] -> ""
  in
  p "(%s" (helper args)

let def_to_str def = p "%s: %s" def.name (args_to_str def.args)
(* Conversion of data types to strings *)

let concatcom s1 s2 = s1 ^ ", " ^ s2

let rec e_to_str (expr : expression) =
  match expr with
  | Val v -> value_to_str v
  | Op (op, elist) -> op_to_str op (List.map e_to_str elist)
  | Var _ -> p "Var"
  | Divide (e1, e2) -> p "Divide (%s, %s)" (e_to_str e1) (e_to_str e2)
  | Let (_, e1, e2) -> p "Let (%s, %s)" (e_to_str e1) (e_to_str e2)
  | IfThenElse (e1, e2, e3) ->
      p "IfThenElse (%s, %s, %s)" (e_to_str e1) (e_to_str e2) (e_to_str e3)
      (* line number not included on error since expression type doesn't contain info field *)
  | Tuple e_list -> (
      match List.map e_to_str e_list with
      | h :: t -> "(" ^ List.fold_left concatcom h t ^ ")"
      | _ -> failwith "tried to take tuple of empty list")
  | Piece e_list -> (
      match List.map e_to_str e_list with
      | h :: t -> "Piece (" ^ List.fold_left concatcom h t ^ ")"
      | _ -> failwith "tried to take tuple of empty list")
  | Mark (e1, e2, e3) ->
      p "Mark_%s (%s, %s)" (e_to_str e1) (e_to_str e2) (e_to_str e3)
  | MarkW (e1, e2, e3) ->
      p "MarkW_%s (%s, %s)" (e_to_str e1) (e_to_str e2) (e_to_str e3)
  | Eval (e1, e2) -> p "Eval_%s (%s)" (e_to_str e1) (e_to_str e2)
  | Squeeze e -> p "Squeeze %s" (e_to_str e)
  | Cake -> "Cake"
  | Union (e1, e2) -> p "Union (%s, %s)" (e_to_str e1) (e_to_str e2)

let rec pat_to_str (pat : pattern) =
  match pat with Var x -> x | List l -> "[" ^ ls l ^ "]"

and ls pat = match pat with h :: t -> pat_to_str h ^ " " ^ ls t | [] -> ""

(* Basic evaluator for expressions that do not contain marks and evals. Currently unneeded *)
(*
let rec simple_evaluator env (e : expression) : value =
  let f = simple_evaluator in
  match e with
  | Val v -> v
  | Op (op, elist) ->
      let vlist = List.map (simple_evaluator env) elist in
      apply_op op vlist
  | Var x -> (
      try List.assoc (var_id x) env
      with Not_found -> failwith "Variable not found!")
  | Divide (e1, e2) -> (
      match (f env e1, f env e2) with
      | Interval i, Point r ->
          let split = divide i r in
          Tup [ Interval (fst split); Interval (snd split) ]
      | _ -> failwith "Simple evaluator failed")
  | Union (e1, e2) -> (
      match (f env e1, f env e2) with
      | Piece pc1, Piece pc2 ->
          assert (pc1.lvl = pc2.lvl);
          Piece { lvl = pc1.lvl; pc = pc1.pc @ pc2.pc }
      | _ -> failwith "Simple evaluator failed")
  | Let (var_list, e1, e2) -> (
      try
        match f env e1 with
        | Tup val_list ->
            let env = List.combine var_list val_list @ env in
            f env e2
        | v -> (
            match var_list with
            | [ x ] -> f ((x, v) :: env) e2
            | _ ->
                failwith
                  "The number of variables and number of assigned values do \
                   not line up")
      with _ ->
        failwith
          "The number of variables and number of assigned values do not line up"
      )
  | IfThenElse (e1, e2, e3) -> (
      match f env e1 with
      | Bool true -> f env e2
      | Bool false -> f env e3
      | _ -> failwith "Cannot evaluate this")
  | Tuple e_list -> Tup (map (f env) e_list)
  | Piece e_list ->
      let f e =
        match f env e with
        | Interval i -> i
        | _ -> failwith "Cannot make a piece out of non-intervals!"
      in
      let v_list = List.map f e_list in
      Piece (make_piece v_list)
  | Cake -> Interval { lvl = Cake; i = { l = (0, None); r = (1, None) } }
  | Mark _ -> failwith "Not allowed here"
  | MarkW _ -> failwith "Not allowed here"
  | Eval _ -> failwith "Not allowed here"
  | Squeeze _ -> failwith "Not allowed here"

let rec simple_eval_env env =
  match env with
  | (p, e) :: t ->
      let env' = simple_eval_env t in
      let new_env = try (p, simple_evaluator env' e) :: env' with _ -> env' in
      new_env
  | [] -> []
*)

(* This concerns converting from pre-expressions (Expressions with named variables) to expressions *)

let rec pattern_contains s p =
  match p with
  | List pat_l ->
      List.fold_left (fun b p -> pattern_contains s p || b) false pat_l
  | Var x -> if x = s then true else false

(*  This substitution should only be used for abbreviations! *)
let rec subs (env : (string * pre_expression) list) (pre_exp : pre_expression) :
    pre_expression =
  match pre_exp with
  | i, Let (plist, e1, e2) ->
      let env' =
        List.filter (fun (x, _) -> not (pattern_contains x (List plist))) env
      in
      (i, Let (plist, subs env e1, subs env' e2))
  | i, Var x -> (
      match List.assoc_opt (pre_var_id x) env with
      | Some e ->
          if is_read_pre x then
            match e with
            | i, Var (N s) -> (i, Var (Read s))
            | _, Var (Read _) -> e
            | _ -> failwith ("Cannot read a non-variable!" ^ pre_var_id x)
          else e
      | None -> (i, Var x))
  | i, Val v -> (i, Val v)
  | i, Abbreviation (x, p_l) -> (i, Abbreviation (x, List.map (subs env) p_l))
  | i, Divide (e1, e2) -> (i, Divide (subs env e1, subs env e2))
  | i, Op (op, elist) -> (i, Op (op, List.map (subs env) elist))
  | i, IfThenElse (e1, e2, e3) ->
      (i, IfThenElse (subs env e1, subs env e2, subs env e3))
  | i, Tuple e_list -> (i, Tuple (List.map (subs env) e_list))
  | i, Mark (e1, e2, e3) -> (i, Mark (subs env e1, subs env e2, subs env e3))
  | i, MarkW (e1, e2, e3) -> (i, MarkW (subs env e1, subs env e2, subs env e3))
  | i, Eval (e1, e2) -> (i, Eval (subs env e1, subs env e2))
  | i, Cake -> (i, Cake)
  | i, Squeeze e -> (i, Squeeze (subs env e))
  | i, Piece e_list -> (i, Piece (List.map (subs env) e_list))
  | i, Union (e1, e2) -> (i, Union (subs env e1, subs env e2))

let rec get_defn (d_l : definition list) (x : string) (i : pre_info) =
  match d_l with
  | h :: t -> if x = h.name then (h, t) else get_defn t x i
  | [] -> failwith (p "Abbreviation %s is not yet defined!" x ^ msg_from_info i)

let subs_abbrv (pre_exp : pre_expression) (arg_l : string list)
    (p_l : pre_expression list) (i : pre_info) =
  let env =
    try List.combine arg_l p_l
    with Invalid_argument _ ->
      failwith
        ("Trying to pair abbreviation arguments that are not the same length!"
       ^ msg_from_info i)
  in
  subs env pre_exp

(* Translates surface language to core language *)
let rec p_to_e (l : int list) (d_l : definition list) (pre_exp : pre_expression)
    (env : (string * int list) list) : expression =
  match pre_exp with
  | _, Val v -> Val v
  | i, Var x -> (
      match x with
      | N str -> (
          try Var (N (List.assoc str env))
          with Not_found ->
            failwith
              (p "Variable \"%s\" not found in environment! %s" str
                 (msg_from_info i)))
      | Read str -> (
          try Var (Read (List.assoc str env))
          with Not_found ->
            failwith
              (p "Variable \"%s\" not found in environment! %s" str
                 (msg_from_info i))))
  | _, Op (op, prelist) ->
      let elist = List.mapi (fun i p -> p_to_e (i :: l) d_l p env) prelist in
      Op (op, elist)
  | i, Abbreviation (x, p_l) ->
      let def, t = get_defn d_l x i in
      p_to_e (0 :: l) t (subs_abbrv def.body def.args p_l i) env
  | _, Divide (e0, e1) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      Divide (e0, e1)
  | _, Union (e0, e1) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      Union (e0, e1)
  | _, Let (plist, e0, e1) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let f, env = pattern_helper env (-1 :: l) plist e0 in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      f e1
  | _, IfThenElse (e0, e1, e2) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      let e2 = p_to_e (2 :: l) d_l e2 env in
      IfThenElse (e0, e1, e2)
  | _, Tuple e_list ->
      let e_list = List.mapi (fun i e -> p_to_e (i :: l) d_l e env) e_list in
      Tuple e_list
  | _, Piece e_list ->
      let e_list = List.mapi (fun i e -> p_to_e (i :: l) d_l e env) e_list in
      Piece e_list
  | _, Mark (e0, e1, e2) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      let e2 = p_to_e (2 :: l) d_l e2 env in
      Mark (e0, e1, e2)
  | _, MarkW (e0, e1, e2) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      let e2 = p_to_e (2 :: l) d_l e2 env in
      MarkW (e0, e1, e2)
  | _, Eval (e0, e1) ->
      let e0 = p_to_e (0 :: l) d_l e0 env in
      let e1 = p_to_e (1 :: l) d_l e1 env in
      Eval (e0, e1)
  | _, Squeeze e ->
      let e = p_to_e (0 :: l) d_l e env in
      Squeeze e
  | _, Cake -> Cake

open Format

let kwd = pp_print_string
let spc = pp_print_space

let rec var_string x =
  match x with
  | n :: [] -> p "%i" n
  | n :: l' -> p "%i:%s" n (var_string l')
  | [] -> ""

let var_formatter f x = kwd f (var_string x)

let var_list_formatter f var_list =
  let rec helper var_list =
    match var_list with
    | x :: [] ->
        var_formatter f x;
        kwd f "]"
    | x :: var_list' ->
        var_formatter f x;
        kwd f "|";
        helper var_list'
    | [] -> kwd f ""
  in
  kwd f "[";
  helper var_list

let rec e_formatter (f : formatter) (e : expression) : unit =
  let fmt f = e_formatter f in
  let spc f = pp_print_break f 1 0 in
  match e with
  | Val v ->
      open_hovbox 0;
      kwd f (value_to_str v);
      close_box ()
  | Var x ->
      open_hovbox 0;
      if is_read x then (
        kwd f "Read";
        spc f)
      else ();
      kwd f "[";
      var_formatter f (var_id x);
      kwd f "]";
      close_box ()
  | Divide (e1, e2) ->
      open_hovbox 0;
      kwd f "Divide";
      kwd f "(";
      fmt f e1;
      kwd f ",";
      spc f;
      fmt f e2;
      kwd f ")";
      close_box ()
  | Let (vlist, e1, e2) ->
      open_hovbox 0;
      kwd f "Let";
      spc f;
      open_hovbox 0;
      var_list_formatter f vlist;
      close_box ();
      spc f;
      kwd f "=";
      pp_print_break f 1 1;
      fmt f e1;
      spc f;
      kwd f "in";
      spc f;
      fmt f e2;
      close_box ()
  | Op (op, [ e1; e2 ]) ->
      open_hovbox 0;
      fmt f e1;
      kwd f (op_as_str op);
      fmt f e2;
      close_box ()
  | Op (op, [ e ]) ->
      open_hovbox 0;
      kwd f (op_as_str op);
      fmt f e;
      close_box ()
  | IfThenElse (e1, e2, e3) ->
      open_hovbox 0;
      kwd f "if";
      spc f;
      fmt f e1;
      spc f;
      kwd f "then";
      spc f;
      open_hovbox 1;
      fmt f e2;
      close_box ();
      spc f;
      kwd f "else";
      spc f;
      open_hovbox 1;
      fmt f e3;
      close_box ();
      close_box ()
  | Tuple e_list ->
      open_hovbox 0;
      kwd f "(";
      tup_formatter f e_list;
      kwd f ")";
      close_box ()
  | Mark (e1, e2, e3) ->
      open_hovbox 0;
      kwd f "Mark";
      spc f;
      kwd f "(";
      fmt f e1;
      kwd f ", ";
      fmt f e2;
      kwd f ", ";
      fmt f e3;
      kwd f ")";
      close_box ()
  | MarkW (e1, e2, e3) ->
      open_hovbox 0;
      kwd f "Markw";
      spc f;
      kwd f "(";
      fmt f e1;
      kwd f ",";
      fmt f e2;
      kwd f ",";
      fmt f e3;
      kwd f ")";
      close_box ()
  | Eval (e1, e2) ->
      open_hovbox 0;
      kwd f "Eval";
      spc f;
      kwd f "(";
      fmt f e1;
      kwd f ",";
      spc f;
      fmt f e2;
      kwd f ")";
      close_box ()
  | Cake ->
      open_hovbox 0;
      kwd f "[0,1]";
      close_box ()
  | Piece e_list ->
      open_hovbox 0;
      kwd f "Piece";
      spc f;
      kwd f "(";
      tup_formatter f e_list;
      kwd f ")";
      close_box ()
  | Union (e1, e2) ->
      open_hovbox 0;
      kwd f "Union";
      spc f;
      kwd f "(";
      fmt f e1;
      kwd f ",";
      spc f;
      fmt f e2;
      kwd f ")";
      close_box ()
  | Squeeze e ->
      open_hovbox 0;
      kwd f "Squeeze";
      spc f;
      fmt f e;
      close_box ()
  | Op (op, l) ->
      open_hovbox 0;
      kwd f (op_as_str op);
      spc f;
      kwd f "(";
      tup_formatter f l;
      kwd f ")";
      close_box ()

and tup_formatter f e_list =
  match e_list with
  | h :: [] -> e_formatter f h
  | h :: t ->
      e_formatter f h;
      kwd f ",";
      spc f ();
      tup_formatter f t
  | [] -> ()
