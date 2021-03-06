type var = int

type formula =
|Var of var
|And of formula*formula
|Or of formula*formula
|Not of formula
|True
|False

let rec subst x b a  = match a with
|Var v when v = x -> b
|And(p1,p2) -> And(subst x b p1, subst x b p2)
|Or(p1,p2) -> Or(subst x b p1, subst x b p2)
|Not(p1) -> Not(subst x b p1)
|Var p -> Var p
|True -> True
  |False -> False

exception Not_found

let rec free_var = function
    |Var v ->  v
    |True -> raise Not_found
    |False -> raise Not_found
    |Not(p) -> free_var p
    |And(p1,p2) -> (try free_var p1;
      with
      |Not_found -> free_var p2;)
     |Or(p1,p2) -> (try free_var p1
      with
      |Not_found -> free_var p2)

let rec eval = function
  |True -> true
  |False -> false
  |Not(p) -> not( eval p)
  | And(p1,p2) -> (eval p1) && (eval p2)
  |Or(p1,p2) ->(eval p1) || (eval p2)
  | Var 0 -> false
    | Var 1 -> true
                            

let rec sat p = try
    let v = free_var p in
      (eval (subst v True p)) ||  (eval (subst v False p))
        with Not_found -> eval p
  
let () =
  let x = Var 0 in
  let x'= Not x in
  let y = Var 1 in
  let y'= Not y in
  let a = And (And(Or (x,y), Or (x',y)), Or (x',y')) in
  let b = And (And(Or (x,y), Or (x',y)), And(Or (x,y'), Or (x',y'))) in
  assert (sat a);
  assert (not (sat b))               
                          
 type literal = bool * var (* false means negated *)
type clause = literal list
type cnf = clause list

let rec list_mem x l = match l with
  |[] -> false
  | y::t -> if x=y then true else list_mem x t

let rec list_map f l = match l with
  |[] -> []
  | y::t ->  (f y)::list_map f t

let rec list_filter f l = match l with
  |[] -> []
  | y::t ->  if f y then y::list_filter f t else list_filter f t


  let () =
  assert (list_mem 2 [1;2;3]);
  assert (not (list_mem 5 [1;2;3]));
  assert (not (list_mem 1 []))

let () =
  assert (list_map (fun x -> 2*x) [1;2;3] = [2;4;6]);
  assert (list_map (fun _ -> ()) [] = [])




let () =
  let even x = x mod 2 = 0 in
  assert (list_filter even [1;2;3;4;6] = [2;4;6])


let subst_cnf (v:var) b (a:cnf) : cnf = match b with
  |true ->     let v_true = (true,v) in
    let v_false = (false,v) in
    let not_v  l = not  (list_mem v_true l)  in
    let a1 = list_filter not_v  a in  (* removes clauses containing v *)
    let different  y = v_false <> y in
    list_map (list_filter different)  a1
  |false ->     let v_false = (true,v) in
    let v_true = (false,v) in
    let not_v  l = not  (list_mem v_true l)  in
    let a1 = list_filter not_v  a in 
    let different  y = v_false <> y in
    list_map (list_filter different)  a1

let rec dpll a =
  try
    let first_clause = List.hd(a) in
    (try
      let first_literal = List.hd(first_clause) in
      let x = snd first_literal in
      dpll (subst_cnf x true a)  ||  dpll (subst_cnf x false a)
    with _ -> false)
  with _ -> true

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert ( not (dpll b))


let rec  unit  = function
  |[] -> raise Not_found
  | y::t -> if List.length y = 1 then List.hd y else
      try
        unit t
      with Not_found -> raise Not_found

let () =
  let x = true, 0 in
  let y = true, 1 in
  let y'= false,1 in
  assert (unit [[x;y]; [x]; [y;y']] = x)

let rec pure_in_clause c a = match c with
  |[] -> raise Not_found
  |x::c' -> let x_bar = not(fst x),snd x in
    let r = list_filter (list_mem x_bar) a in
    if List.length r = 0 then x else pure_in_clause c' a
        
           

let rec pure_aux a a_ori = match a with
  |[] -> raise Not_found
  | c::t -> try pure_in_clause c a_ori
    with Not_found -> pure_aux t a_ori

let pure a = pure_aux a a

let rec new_dpll  (a:cnf) = match a with
  |[] -> true
  |_ -> let isEmpty l = (List.length l = 0) in
    let r = list_filter isEmpty a in
    if (List.length r) > 0 then false
    else (
      try (
        let unitliteral = (unit a)  in
        let x = snd (unitliteral) in
        let bl = fst  unitliteral in
        new_dpll (subst_cnf x bl a)
      )
      with Not_found -> (
      try
        let pure_lit = pure a in
          let x = snd pure_lit  in
        let bl = fst  pure_lit in
         new_dpll (subst_cnf x bl a)
      with Not_found ->
        let first_literal = List.hd( List.hd a ) in
        let x = snd first_literal in
        new_dpll (subst_cnf x true a)  ||  new_dpll (subst_cnf x false a)
    )
    )
  
(** Parse a CNF file. *)
let parse f : cnf =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  in
  let f = load_file f in
  let f = String.map (function '\t' -> ' ' | c -> c) f in
  let f = String.split_on_char '\n' f in
  let f = List.map (String.split_on_char ' ') f in
  let f = List.filter (function "c"::_ | "p"::_ -> false | _ -> true) f in
  let f = List.flatten f in
  let aux (a,c) = function
    | "" -> (a,c)
    | "0" -> (c::a,[])
    | n ->
       let n = int_of_string n in
       let x = if n < 0 then (false,-n) else (true,n) in
       (a,x::c)
  in
  fst (List.fold_left aux ([],[]) f)


let () = assert (new_dpll (parse Sys.argv.(0)))
