type var = string

type t =
  |Var of var
  |App of t*t
  |Abs of var*t

let rec to_string (exp:t) = match exp with
|Var x -> x
|App(t1,t2) ->  "("^to_string(t1) ^ " " ^ to_string(t2) ^")"
|Abs(x,t) -> "(λ"^x^"."^to_string(t) ^")"

(*Question 1.2 *)
let rec has_fv (x:var) t = match t with
|Var y when y=x -> true
|Var y -> false
|App(t1,t2) -> has_fv x t1 ||  has_fv x t2
|Abs(y,t1) when y = x -> false
|Abs(y, t1) -> has_fv x t1

let rec list_vars = function (* returns list of variables in term (may have duplicates) *)
|Var y -> [y]
|App(t1,t2) -> list_vars t1 @  list_vars t2
|Abs(y, t1) -> [y]@ list_vars t1

let list_free_vars t =   (* returns list of free variables in term  *)
  let filter_func x = has_fv x t in 
  List.sort_uniq compare (List.filter filter_func (list_vars t) )



(* Question 1.3 *)

let fresh = 
  let x = ref 0 in
  fun () -> let r = !x in 
            x := r+1;
          "x" ^ string_of_int r

let rec fresh_var t =  (* returns a variable not present in t *)
  let existing_vars = list_vars t in
  let curr_var = fresh () in
  if List.mem curr_var existing_vars then fresh_var t 
  else curr_var 

let rec fresh_var_2 t1 t2 =  (* returns a variable not present in t1 and t2 *)
  let existing_vars = (list_vars t1) @ list_vars t2 in
  let curr_var = fresh () in
  if List.mem curr_var existing_vars then fresh_var_2 t1 t2
  else curr_var 

(* Question 1.4 *)

let rec sub (x:var) u = function
|Var y when y =x -> u
|Var y -> Var y
|App(t1,t2) -> App(sub x u t1, sub x u t2)
|Abs(y,t1) when y = x -> Abs(y,t1)
| Abs(y,t1) when  not (has_fv y u) -> Abs(y, sub x u t1)
| Abs(y,t1) ->  
             let newy =  fresh_var t1 in 
             let newt1 = sub y (Var newy) t1 in
             Abs(newy, sub x u newt1 )


let rec red = function
|App(Abs(x,t), u) -> Some (sub x u t)
|App(t1, t2) -> (match red t1 with 
                |None -> (match red t2 with
                            |None ->None
                            |Some t -> Some (App (t1, t))
                              )
                |Some t -> Some (App(t,t2))
                  )
|Abs(x, t) -> (match red t with 
                |None -> None
                |Some t1 -> Some (Abs(x,t1))
                  )
|_ -> None

let rec normalize t = match red t with
| None -> t
| Some t1 -> normalize t1

let reduction t = 
  print_endline(to_string t);
  let n = ref 0 in
  let rec real_reduction tt =
    match tt with
    | None -> ()
    | Some t1 ->  n := !n + 1;
                  print_endline("-> "^ to_string t1);
                  real_reduction (red t1)
    in real_reduction (red t);
    print_endline (string_of_int(!n)^ " reduction steps")

  
(* Question 1.6 

let eq t1 t2 = 
  let nt1 = normalize t1 in 
  let nt2 = normalize t2 in 
  nt1 = nt2

  *)

  (* Question 1.7 *)



let rec has_v (x:var) t = match t with (* returns true iif var appears in term *)
|Var y when y=x -> true
|Var y -> false
|App(t1,t2) -> has_v x t1 ||  has_v x t2
|Abs(y,t1) when y = x -> true
|Abs(y, t1) -> has_v x t1


let rec alpha p1 p2 = match p1,p2 with
  |(Var x, Var y) when x =y -> true
  | (Var x, Var y)  -> false
  | (App(t1,t2), App(j1,j2)) -> alpha t1 j1 && alpha t2 j2
  |(Abs(x,t1), Abs(y, t2)) when x =y -> alpha t1 t2
  |(Abs(x,t1), Abs(y, t2)) -> let newxy = ( fresh_var_2 p1  p2 ) in 
                              let newt1 =  sub x (Var newxy) t1 in 
                              let newt2 = sub y (Var newxy) t2 in 
                              alpha newt1 newt2
  |_ -> false

let eq t1 t2 = 
  let nt1 = normalize t1 in 
  let nt2 = normalize t2 in 
  alpha nt1  nt2

let id = Abs("x", Var "x")

let btrue = Abs("x",Abs("y",Var "x"))
let bfalse = Abs("x",Abs("y",Var "y"))

let rec abss l t = match l with 
|[] -> t 
| x::a -> Abs(x, abss a t) 

let apps l = 
  let lrev = List.rev l in 
  let rec apps_rev = function 
   | [a] -> a 
   | hd::tl -> App(apps_rev tl, hd) 
   | _ -> id   in 
   apps_rev lrev 

let bif = Abs("b",Abs("x",Abs("y", App(App(Var "b", Var "x"), Var "y"))))

let nat n = 
   let rec comp f x = function 
   |0 -> x
  | p -> App(f,(comp f x (p-1)))
  in 
  Abs("f",Abs("x", (comp (Var "f") (Var "x") n)))

let succ = Abs("n",Abs("f",Abs("x", App(Var "f", apps [Var"n"; Var "f"; Var "x"]))))

let add = Abs("n", Abs("m", Abs("f", Abs("x", App(App(Var "n", Var "f"), apps [Var"m"; Var "f"; Var "x"])))))

let mul = Abs("n", Abs("m", Abs("f", Abs("x", apps [Var "n"; App(Var "m", Var "f"); Var "x"]))))

(* The exact number of reductions is 2*n + 4, n being the first number. This can be calculated exactly from the formula of mul*)
(* 4 reductions to replace n, m, then mf and x, then we need to reduce mf (mf (... mf (x))), each mf is 2 reductions, and there n of them, so 2*n reduction *)

let iszero = Abs("n",Abs("x",Abs("y",apps [Var "n"; Abs("z",Var "y"); Var "x"])))

let pair = Abs("x", Abs("y", Abs("b", apps [bif; Var "b"; Var "x"; Var "y"])))

let fst = Abs("p", apps [Var "p"; btrue])
let snd = Abs("p", apps [Var "p"; bfalse])

let rec fib_naive = function
|0 -> 0 
| 1 -> 1 
| n -> (fib_naive (n-1)) + (fib_naive (n-2))

let fib_fun (x,y) = y,x+y 

let fib n = 
  let c = ref (0,1) in 
  for i = 1 to n do 
    c := fib_fun !c
  done;
  Pervasives.fst !c

let pred_fun = Abs("p",apps [pair; App(snd, Var "p"); App(succ, App(snd, Var "p"))])

let pred = Abs("n", apps [bif; App(iszero, Var "n"); Var "n"; App(fst, apps[Var"n"; pred_fun; apps[pair; nat 0; nat 0]])])

let subs = Abs("n", Abs("m", apps [Var "m"; pred; Var "n"]))

let fact_fun f = function 
| 0 -> 1
| n -> n*f(n-1)

let rec fix f n = f (fix f) n

let fact n = fix fact_fun n

let fixpoint = Abs("f", App(Abs("x", App(Var"f", App(Var "x", Var "x"))), Abs("x",  App(Var"f", App(Var "x", Var "x")))))

let factorial = App(fixpoint, Abs("f",Abs("n", apps[bif; App(iszero, Var "n"); nat 1; apps[mul;Var "n"; App(Var "f", App(pred,Var "n"))]])))

(* Part 3 *)
type dvar = int

type db =
  | DVar of dvar
  | DApp of db * db
  | DAbs of db

let index_ofx x l = 
  let i = ref 0 in 
  let rec ind = function 
                |y::tl when y = x -> !i
                |[] -> -1
                |y::tl ->  i := !i+1;  
                ind tl in
  ind l

let db_of_term t =
  let freevars = ref (list_free_vars t) in 
  let rec db_of_term_rec = function 
  |Var x -> 
          DVar (index_ofx x !freevars)
  |App(t1, t2) -> DApp (db_of_term_rec t1, db_of_term_rec t2)
  |Abs(x,t1) -> freevars := [x]@ !freevars;
                let db1 = db_of_term_rec t1 in 
                freevars :=  List.filter (fun y -> y != x) !freevars;
                DAbs db1
                in 
                db_of_term_rec t

let lift n t = 
  let depth = ref 0 in 
  let rec lift_rec  = function 
    |DVar x -> if(x >= !depth && x >= n) then DVar(x+1) else DVar(x) 
    |DApp(t1, t2) -> DApp (lift_rec t1, lift_rec t2)
    |DAbs t1 -> depth := !depth + 1;
      let db1 = lift_rec t1  in 
      depth :=  !depth - 1;
      DAbs db1
  in 
  lift_rec t
                  
let rec to_string_db = function 
| DVar x -> string_of_int x
|DApp(t,p) -> "("^to_string_db t ^ ")  (" ^ to_string_db p ^" )"
|DAbs t -> "(λ."^ to_string_db t

(* tests *)

let () =
  let t = lift 0 (DAbs (DApp (DVar 0, DVar 1))) in
  let t' = DAbs (DApp (DVar 0, DVar 2)) in
  assert (t = t')
    
let () =
    let t = Abs ("x", Abs ("y", App (App (Var "x", Abs ("z", Var "x")), Abs ("x", App (Var "x", Var "y"))))) in
    let t' = DAbs (DAbs (DApp (DApp (DVar 1, DAbs (DVar 2)), DAbs (DApp (DVar 0, DVar 1))))) in
    print_endline (to_string_db(db_of_term t));
    assert (db_of_term t = t')

let () = assert (eq (App (factorial, nat 5)) (nat 120))


(* 
let () =
  let t = Var "t" in
  reduction (apps [fixpoint; t])

  *)


let () = assert (fact 5 = 120)


let () =
  assert (eq (apps [subs; nat 14; nat 5]) (nat 9))

let () =
  assert (eq (apps [pred; nat 11]) (nat 10));
  assert (eq (apps [pred; nat 0]) (nat 0))
let () =
  assert (eq (apps [pred_fun; apps [pair; nat 1; nat 5]]) (apps [pair; nat 5; nat 6]))

let () = assert (fib 10 = 55)

let () = assert (fib_naive 10 = 55)


let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [fst; apps [pair; t; u]]) t);
  assert (eq (apps [snd; apps [pair; t; u]]) u)

let () =
  assert (eq (apps [iszero; nat 5]) bfalse);
  assert (eq (apps [iszero; nat 0]) btrue)

let () = reduction (apps [mul; nat 3; nat 100])


let () =
  assert (eq (apps [mul; nat 3; nat 4]) (nat 12))
let () =
  assert (eq (apps [add; nat 6; nat 5]) (nat 11))
let () =
  assert (eq (apps [succ; nat 5]) (nat 6))

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [bif; btrue; t; u]) t);
  assert (eq (apps [bif; bfalse; t; u]) u)


let () =
  let t = Var "t" in
  let u = Var "u" in
  let v = Var "v" in
  let w = Var "w" in
  assert (apps [t; u; v; w] = App (App (App (t, u), v), w))

  
let () =
  let t = Var "t" in
  assert (abss ["x"; "y"; "z"] t = Abs ("x", Abs ("y", Abs ("z", t))))


let () =
  let t = App (Abs ("x", Abs ("y", Var "x")), Var "y") in
  print_endline (to_string (normalize t));
  assert (eq t (Abs ("z", Var "y")))


let () =
  assert (alpha (Abs ("x", Var "x")) (Abs ("y", Var "y")));
  assert (not (alpha (Abs ("x", Var "x")) (Abs ("x", Var "y"))));
  let x = "x" in
  let y = "y" in 
  assert(alpha (Abs(y, Abs(x, App(Var x, Var y)))) (Abs(x, Abs(y, App(Var y, Var x)))) )
  





let _ =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  reduction (App (id2, id2))
    

let () =
  print_endline (to_string (Abs ("x", App (Var "y", Var "x"))));
  print_endline (to_string (App (Abs ("x", Var "y"), Var "x")))

let () =
let t = App (Var "x", Abs ("y", App (Var "y", Var "z"))) in
assert (has_fv "x" t);
assert (not (has_fv "y" t));
assert (has_fv "z" t);
assert (not (has_fv "w" t))

let () =
print_endline (fresh () );
print_endline (fresh () );
print_endline (fresh () )

let () =
  let t = App (Var "x", Abs ("y", Var "x")) in
  let i = Abs ("x", Var "x") in
  let ti = App (Abs ("x", Var "x"), Abs ("y", Abs ("x", Var "x"))) in
  assert (sub "x" i t = ti);
  assert (not (sub "x" (Var "y") (Abs ("y", Var "x")) = Abs("y", Var "y")))

