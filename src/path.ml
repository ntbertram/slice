open Basic
open Ast

type path =
  | Val of value
  | Op of op * path list
  | Var of variable
  | Divide of path * path
  | Let of binding_variable list * path * path
  | Assert of path * path
  | Tuple of path list
  | Mark of int * path * path
  | MarkW of int * path * path
  | Squeeze of path
  | Eval of int * path
  | Piece of path list
  | Cake
  | Union of path * path

let rec max_depth path =
  match path with
  | Divide (p1, p2) -> max (max_depth p1) (max_depth p2) + 1
  | Let (_, p1, p2) -> max (max_depth p1) (max_depth p2) + 1
  | Op (_, pl) -> List.fold_left (fun m p -> max m (max_depth p)) 0 pl + 1
  | Assert (p1, p2) -> max (max_depth p1) (max_depth p2) + 1
  | Tuple pl -> List.fold_left (fun m p -> max m (max_depth p)) 0 pl + 1
  | Piece pl -> List.fold_left (fun m p -> max m (max_depth p)) 0 pl + 1
  | Squeeze p -> max_depth p + 1
  | Mark (_, p1, p2) -> max (max_depth p1) (max_depth p2) + 1
  | MarkW (_, p1, p2) -> max (max_depth p1) (max_depth p2) + 1
  | Eval (_, p) -> max_depth p + 1
  | Union (p1, p2) -> max (max_depth p1) (max_depth p2) + 1
  | _ -> 0

type pre_path =
  | Val of value
  | Op of op * pre_path list
  | Var of variable
  | Divide of pre_path * pre_path
  | Let of binding_variable list * pre_path * pre_path
  | Assert of pre_path * pre_path
  | Tuple of pre_path list
  | Mark of pre_path * pre_path * pre_path
  | MarkW of pre_path * pre_path * pre_path
  | Eval of pre_path * pre_path
  | Piece of pre_path list
  | Squeeze of pre_path
  | Cake
  | Union of pre_path * pre_path

(* Basic evaluator for expressions that do not contain marks and evals *)
let rec pre_path_evaluator env (e : pre_path) : value =
  let f = pre_path_evaluator in
  match e with
  | Val v -> v
  | Var x -> List.assoc (var_id x) env
  | Divide (e1, e2) -> (
      match (f env e1, f env e2) with
      | Interval i, Point r ->
          let split = divide i r in
          Tup [ Interval (fst split); Interval (snd split) ]
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
  | Op (op, elist) ->
      let vlist = List.map (pre_path_evaluator env) elist in
      apply_op op vlist
  | Assert (_, e) -> f env e
  | Tuple e_list -> Tup (List.map (f env) e_list)
  | Piece e_list ->
      let v_list = List.map (f env) e_list in
      (*Piece (List.map (fun e ->
        (match f env e with
        | Interval i ->  i
        | _              -> failwith "Cannot simple eval this")) e_list)*)
      let get_piece v =
        match v with
        | Interval i -> i
        | _ -> failwith "Cannot form a piece containing a non-interval"
      in
      let i_list = List.map get_piece v_list in
      Piece (make_piece i_list)
  | Union (e1, e2) -> (
      match (f env e1, f env e2) with
      | Piece pc1, Piece pc2 ->
          assert (pc1.lvl = pc2.lvl);
          Piece { lvl = pc1.lvl; pc = pc1.pc @ pc2.pc }
      | _ -> failwith "Cannot simply evaluate this")
  | Cake -> Interval { lvl = Cake; i = { l = (0, None); r = (1, None) } }
  | Mark _ -> failwith "Not allowed here"
  | MarkW _ -> failwith "Not allowed here"
  | Eval _ -> failwith "Not allowed here"
  | Squeeze _ -> failwith "Not allowed here"

let rec pre_path_to_path env (e : pre_path) : path =
  let f = pre_path_to_path in
  match e with
  | Val v -> Val v
  | Op (op, elist) -> Op (op, List.map (f env) elist)
  | Var l -> Var l
  | Divide (e1, e2) -> Divide (f env e1, f env e2)
  | Union (e1, e2) -> Union (f env e1, f env e2)
  | Let (l, e1, e2) -> Let (l, f env e1, f env e2)
  | Assert (e1, e2) -> Assert (f env e1, f env e2)
  | Tuple e_list -> Tuple (List.map (f env) e_list)
  | Piece e_list -> Piece (List.map (f env) e_list)
  | Squeeze e -> Squeeze (f env e)
  | Mark (e1, e2, e3) ->
      let n =
        match pre_path_evaluator env e1 with Num n -> n | _ -> failwith "NO"
      in
      Mark (n, f env e2, f env e3)
  | MarkW (e1, e2, e3) ->
      let n =
        match pre_path_evaluator env e1 with Num n -> n | _ -> failwith "NO"
      in
      MarkW (n, f env e2, f env e3)
  | Eval (e1, e2) ->
      let n =
        match pre_path_evaluator env e1 with Num n -> n | _ -> failwith "NO"
      in
      Eval (n, f env e2)
  | Cake -> Cake

(* This enumerates all combinations of one list with the rest, similar to a cartesian product of sets*)
let rec all_combinations (l : 'a list list) =
  match l with
  | l1 :: rest ->
      let rest_comb = all_combinations rest in
      let append_all a = List.map (fun comb -> a :: comb) rest_comb in
      let new_combinations = List.map (fun a -> append_all a) l1 in
      List.concat new_combinations
  | [] -> [ [] ]

let all_pairs (l1, l2) =
  let pairs = all_combinations [ l1; l2 ] in
  List.map
    (fun l -> match l with [ a1; a2 ] -> (a1, a2) | _ -> failwith "Ekh")
    pairs

let all_triplets (l1, l2, l3) =
  let triplets = all_combinations [ l1; l2; l3 ] in
  List.map
    (fun l ->
      match l with [ a1; a2; a3 ] -> (a1, a2, a3) | _ -> failwith "Ekh")
    triplets

let expression_to_path_list (e : expression) : path list =
  let rec helper (e : expression) =
    let f = helper in
    match e with
    | Val v -> [ Val v ]
    | Cake -> [ Cake ]
    | Var l -> [ Var l ]
    | Op (op, elist) ->
        List.map (fun l -> Op (op, l)) (all_combinations (List.map f elist))
    | Divide (e1, e2) ->
        List.map (fun (e1, e2) -> Divide (e1, e2)) (all_pairs (f e1, f e2))
    | Let (l, e1, e2) ->
        List.map (fun (e1, e2) -> Let (l, e1, e2)) (all_pairs (f e1, f e2))
    | Mark (e0, e1, e2) ->
        List.map
          (fun (e0, e1, e2) -> Mark (e0, e1, e2))
          (all_triplets (f e0, f e1, f e2))
    | MarkW (e0, e1, e2) ->
        List.map
          (fun (e0, e1, e2) -> MarkW (e0, e1, e2))
          (all_triplets (f e0, f e1, f e2))
    | Eval (e0, e) ->
        List.map (fun (e0, e) -> Eval (e0, e)) (all_pairs (f e0, f e))
    | Tuple l -> List.map (fun l -> Tuple l) (all_combinations (List.map f l))
    | Piece l -> List.map (fun l -> Piece l) (all_combinations (List.map f l))
    | Union (e1, e2) ->
        List.map (fun (e1, e2) -> Union (e1, e2)) (all_pairs (f e1, f e2))
    | Squeeze e -> List.map (fun e -> Squeeze e) (f e)
    | IfThenElse (e1, e2, e3) ->
        List.map (fun (e1, e2) -> Assert (e1, e2)) (all_pairs (f e1, f e2))
        @ List.map
            (fun (e1, e3) -> Assert (Op (Not, [ e1 ]), e3))
            (all_pairs (f e1, f e3))
  in
  List.map (pre_path_to_path []) (helper e)

type 'a seq = Nil | Cons of ('a * (unit -> 'a seq))

let rec list_to_seq = function
  | [] -> Nil
  | h :: t -> Cons (h, fun () -> list_to_seq t)

(* let hd (s : 'a seq) = match s with Nil -> failwith "hd" | Cons (h, _) -> h
   let tl (s : 'a seq) = match s with Nil -> failwith "tl" | Cons (_, t) -> t () *)

let s1 = Cons (1, fun () -> Cons (2, fun () -> Cons (3, fun () -> Nil)))
let s2 = Cons (4, fun () -> Cons (5, fun () -> Cons (6, fun () -> Nil)))

let rec concat_seq s1 s2 =
  match s1 with
  | Nil -> s2
  | Cons (h, t) -> Cons (h, fun () -> concat_seq (t ()) s2)

let rec flatten (seqs : 'a seq seq) : 'a seq =
  (* print_endline "hi"; *)
  match seqs with
  | Nil -> Nil
  | Cons (h, t) ->
      let rec aux s1 s2 =
        match s1 with
        | Nil -> flatten (s2 ())
        | Cons (x, xt) -> Cons (x, fun () -> aux (xt ()) s2)
      in
      aux h t
(* concat_seq h (flatten (t ())) *)

let size_seq s =
  let rec aux acc s =
    match s with Nil -> acc | Cons (_, t) -> aux (acc + 1) (t ())
  in
  aux 0 s

let rec map_seq f s =
  match s with
  | Nil -> Nil
  | Cons (h, t) -> Cons (f h, fun () -> map_seq f (t ()))

let rec all_combinations_seq (seqs : 'a seq list) : 'a list seq =
  match seqs with
  | [] -> Cons ([], fun () -> Nil)
  | h :: t ->
      let rest_comb = all_combinations_seq t in
      let append_all a = map_seq (fun comb -> a :: comb) rest_comb in
      let new_combinations = map_seq (fun x -> append_all x) h in
      flatten new_combinations

let all_pairs_seq s1 s2 =
  let pairs = all_combinations_seq [ s1; s2 ] in
  map_seq
    (fun l -> match l with [ a1; a2 ] -> (a1, a2) | _ -> failwith "Ekh")
    pairs

let all_triplets_seq s1 s2 s3 =
  let triplets = all_combinations_seq [ s1; s2; s3 ] in
  map_seq
    (fun l ->
      match l with [ a1; a2; a3 ] -> (a1, a2, a3) | _ -> failwith "Ekh")
    triplets

let rec expression_to_pre_path_seq (e : expression) : pre_path seq =
  let f = expression_to_pre_path_seq in
  match e with
  | Cake -> Cons (Cake, fun () -> Nil)
  | Val v -> Cons (Val v, fun () -> Nil)
  | Var l -> Cons (Var l, fun () -> Nil)
  | Op (op, e_list) ->
      map_seq
        (fun e_list -> Op (op, e_list))
        (all_combinations_seq (List.map f e_list))
  | Divide (e1, e2) ->
      map_seq (fun (e1, e2) -> Divide (e1, e2)) (all_pairs_seq (f e1) (f e2))
  | Let (l, e1, e2) ->
      map_seq (fun (e1, e2) -> Let (l, e1, e2)) (all_pairs_seq (f e1) (f e2))
  | Mark (e0, e1, e2) ->
      map_seq
        (fun (e0, e1, e2) -> Mark (e0, e1, e2))
        (all_triplets_seq (f e0) (f e1) (f e2))
  | MarkW (e0, e1, e2) ->
      map_seq
        (fun (e0, e1, e2) -> MarkW (e0, e1, e2))
        (all_triplets_seq (f e0) (f e1) (f e2))
  | Eval (e0, e) ->
      map_seq (fun (e0, e) -> Eval (e0, e)) (all_pairs_seq (f e0) (f e))
  | Tuple l -> map_seq (fun l -> Tuple l) (all_combinations_seq (List.map f l))
  | Piece l -> map_seq (fun l -> Piece l) (all_combinations_seq (List.map f l))
  | Union (e1, e2) ->
      map_seq (fun (e1, e2) -> Union (e1, e2)) (all_pairs_seq (f e1) (f e2))
  | Squeeze e -> map_seq (fun e -> Squeeze e) (f e)
  | IfThenElse (e1, e2, e3) ->
      [
        (* map_seq (fun e1 -> Nop e1) (f e1); *)
        (* map_seq (fun e1 -> PrunedT e1) (f e1);
           map_seq (fun e1 -> PrunedF e1) (f e1); *)
        map_seq (fun (e1, e2) -> Assert (e1, e2)) (all_pairs_seq (f e1) (f e2));
        map_seq
          (fun (e1, e3) -> Assert (Op (Not, [ e1 ]), e3))
          (all_pairs_seq (f e1) (f e3));
      ]
      |> list_to_seq |> flatten

let pre_path_to_path_seq seq = map_seq (pre_path_to_path []) seq

let rec num_paths (e : expression) =
  match e with
  | Val _ -> 1
  | Var _ -> 1
  | Op (_, e_list) -> List.fold_left ( * ) 1 (List.map num_paths e_list)
  | Divide (e1, e2) -> num_paths e1 * num_paths e2
  | Let (_, e1, e2) -> num_paths e1 * num_paths e2
  | IfThenElse (e1, e2, e3) -> num_paths e1 * (num_paths e2 + num_paths e3)
  | Tuple e_list -> List.fold_left ( * ) 1 (List.map num_paths e_list)
  | Mark (e0, e1, e2) -> num_paths e0 * num_paths e1 * num_paths e2
  | MarkW (e0, e1, e2) -> num_paths e0 * num_paths e1 * num_paths e2
  | Eval (e0, e) -> num_paths e0 * num_paths e
  | Cake -> 1
  | Piece e_list -> List.fold_left ( * ) 1 (List.map num_paths e_list)
  | Union (e1, e2) -> num_paths e1 * num_paths e2
  | Squeeze e -> num_paths e

let num_paths2 (e : expression) =
  let count = ref 0 in
  let pre_path_seq = expression_to_pre_path_seq e in
  let path_seq = pre_path_to_path_seq pre_path_seq in
  let rec helper (s : path seq) =
    print_endline (string_of_int !count);
    match s with
    | Nil -> ()
    | Cons (_, t) ->
        count := !count + 1;
        helper (t ())
  in
  helper path_seq;
  print_endline (string_of_int !count)

let rec unique_ifs (visited : expression list ref) (e : expression) =
  match e with
  | Val _ -> ()
  | Var _ -> ()
  | Divide (e1, e2) ->
      unique_ifs visited e1;
      unique_ifs visited e2
  | Let (_, e1, e2) ->
      unique_ifs visited e1;
      unique_ifs visited e2
  | Op (_, e_list) -> List.iter (unique_ifs visited) e_list
  | IfThenElse (e1, e2, e3) ->
      if List.mem e1 !visited then () else visited := e1 :: !visited;
      unique_ifs visited e1;
      unique_ifs visited e2;
      unique_ifs visited e3
  | Tuple e_list -> List.iter (unique_ifs visited) e_list
  | Mark (e0, e1, e2) ->
      unique_ifs visited e0;
      unique_ifs visited e1;
      unique_ifs visited e2
  | MarkW (e0, e1, e2) ->
      unique_ifs visited e0;
      unique_ifs visited e1;
      unique_ifs visited e2
  | Eval (e0, e) ->
      unique_ifs visited e0;
      unique_ifs visited e
  | Cake -> ()
  | Piece e_list -> List.iter (unique_ifs visited) e_list
  | Union (e1, e2) ->
      unique_ifs visited e1;
      unique_ifs visited e2
  | Squeeze _ -> ()

let count_unique_ifs (e : expression) =
  let visited = ref [] in
  unique_ifs visited e;
  List.length !visited

let p = Printf.sprintf
let concatcom s1 s2 = s1 ^ ", " ^ s2

let rec path_to_str (path : path) =
  match path with
  | Val v -> value_to_str v
  | Var _ -> p "Var"
  | Op (op, elist) -> op_to_str op (List.map path_to_str elist)
  | Divide (e1, e2) -> p "Divide (%s, %s)" (path_to_str e1) (path_to_str e2)
  | Squeeze e -> p "Squeeze %s" (path_to_str e)
  | Let (_, e1, e2) -> p "Let (%s, %s)" (path_to_str e1) (path_to_str e2)
  | Assert (e1, e2) ->
      p "T(%s, %s)" (path_to_str e1) (path_to_str e2)
      (* line number not included on error since expression type doesn't contain info field *)
  | Tuple e_list -> (
      match List.map path_to_str e_list with
      | h :: t -> "(" ^ List.fold_left concatcom h t ^ ")"
      | _ -> failwith "tried to take tuple of empty list")
  | Piece e_list -> (
      match List.map path_to_str e_list with
      | h :: t -> "Piece (" ^ List.fold_left concatcom h t ^ ")"
      | _ -> failwith "tried to take tuple of empty list")
  | Mark (n, e2, e3) -> p "Mark_%i(%s, %s)" n (path_to_str e2) (path_to_str e3)
  | MarkW (n, e2, e3) ->
      p "MarkW_%i(%s, %s)" n (path_to_str e2) (path_to_str e3)
  | Eval (n, e2) -> p "Eval_%i(%s)" n (path_to_str e2)
  | Cake -> "Cake"
  | Union (e1, e2) -> p "Union (%s, %s)" (path_to_str e1) (path_to_str e2)
