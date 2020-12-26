type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string = function
  |Type -> "Type"
  |Nat -> "Nat"
  |Var v -> v 
  |App(t1, t2) -> ""^to_string(t1) ^ " " ^ to_string(t2) ^""
  |Abs(x,xtype,t) ->  "(fun ("^x^" : "^(to_string xtype)^") -> "^(to_string t)^")"
  |Pi(x,t1,t2) ->  "(("^x^" : "^to_string t1 ^") -> "^to_string t2^")"
  |Z -> "Z"
  |S(t) -> "(S "^ (to_string t)  ^")"
  |Ind(t1,t2,t3,t4) -> "(Ind "^(to_string t1)^" , "^(to_string t2) ^" , "^(to_string t3)^" , "^(to_string t4)^")"
  |Eq(t1,t2) -> "Eq ("^to_string(t1) ^ ") (" ^ to_string(t2) ^")"
  |Refl(t) -> "Refl "^(to_string(t))
  |J(t1,t2,t3,t4,t5) -> "(J "^(to_string t1)^" , "^(to_string t2) ^" , "^(to_string t3)^" , "^(to_string t4)^" , "^ (to_string t5)^")"

(* Q 5.3 *)
let  fresh_var = 
  let x = ref 0 in
    fun () -> let r = !x in 
              x := r+1;
            "x" ^ string_of_int r

let rec list_vars = function (* returns list of variables in term (may have duplicates) *)
|Var y -> [y]
|Type -> []
|Nat -> []
|App(t1,t2) -> list_vars t1 @  list_vars t2
|Abs(y,ty, t1) -> [y]@ list_vars ty @ list_vars t1
|Pi(y, ty, t1) -> [y]@ list_vars ty @ list_vars t1
|Z -> []
|S(t) -> list_vars t
|Ind(t1,t2,t3,t4) -> (list_vars t1)@(list_vars t2)@(list_vars t3)@(list_vars t4)
|Eq(t1,t2) -> list_vars t1 @  list_vars t2
|Refl(t) -> list_vars t
|J(t1,t2,t3,t4,t5) -> (list_vars t1)@(list_vars t2)@(list_vars t3)@(list_vars t4)@(list_vars t5)

let rec fresh t =  (* returns a variable not present in t *)
  let existing_vars = list_vars t in
  let curr_var = fresh_var () in
  if List.mem curr_var existing_vars then fresh t 
  else curr_var

let rec fresh_2 t1 t2 =  (* returns a variable not present in t1 and t2 *)
  let existing_vars = (list_vars t1) @ list_vars t2 in
  let curr_var = fresh_var () in
  if List.mem curr_var existing_vars then fresh_2 t1 t2
  else curr_var 

let rec has_fv (x:var) t = match t with
|Type -> false
|Nat -> false
|Var y when y=x -> true
|Var y -> false
|App(t1,t2) -> has_fv x t1 ||  has_fv x t2
|Abs(y,ytype,t1) when y = x -> false
|Abs(y,ytype, t1) ->  has_fv x ytype || has_fv x t1
|Pi(y, ytype, t1) when y = x -> false 
|Pi(y, ytype, t1) -> has_fv x ytype || has_fv x t1
|Z -> false
|S(t) -> has_fv x t
|Ind(t1,t2,t3,t4) -> has_fv x t1 || has_fv x t2 || has_fv x t3 || has_fv x t4
|Eq(t1,t2) -> has_fv x t1 ||  has_fv x t2
|Refl(t) -> has_fv x t
|J(t1,t2,t3,t4,t5) -> has_fv x t1 || has_fv x t2 || has_fv x t3 || has_fv x t4 || has_fv x t5

(* Q 5.4 *)

let rec subst x t = function 
|Type -> Type
|Nat -> Nat
|Var y when y =x -> t
|Var y -> Var y
|App(t1,t2) -> App(subst x t t1, subst x t t2)
|Abs(y,yty,t1) when y = x -> Abs(y,yty,t1)
|Abs(y,yty,t1) when  not (has_fv y t) -> Abs(y,subst x t yty, subst x t t1)
| Abs(y,yty,t1) ->  
             let newy =  fresh t1 in 
             let newt1 = subst y (Var newy) t1 in
             Abs(newy,yty, subst x t newt1 )
|Pi(y,yty, t1) when y = x -> Pi(y,yty, t1)
|Pi(y ,yty, t1) when not (has_fv y t) -> Pi(y, subst x t yty, subst x t t1)
|Pi(y ,yty, t1) ->  let newy =  fresh t1 in 
             let newt1 = subst y (Var newy) t1 in
             Pi(newy,subst x t yty, subst x t newt1 )
|Z -> Z
|S(e) -> S(subst x t e )
|Ind(t1,t2,t3,t4) -> Ind(subst x t t1, subst x t t2, subst x t t3,subst x t t4)
|Eq(t1,t2) -> Eq(subst x t t1, subst x t t2)
|Refl(t1) -> Refl(subst x t t1)
|J(t1,t2,t3,t4,t5) -> J(subst x t t1, subst x t t2, subst x t t3,subst x t t4, subst x t t5)

(* Q 5.5 *)

type context = (var * (expr * expr option)) list

let rec string_of_context = function 
|[] -> ""
|(x, (e1, Some e2))::l -> string_of_context l ^"\n"^x^" : "^(to_string e1)^" = "^(to_string e2)
|(x, (e1, None))::l -> string_of_context l^"\n"^x^" : "^(to_string e1)

(* Q 5.6*)

let rec normalize' cont = function 
|Type -> Type
|Nat -> Nat
|Var x ->  (try (match (List.assoc x (List.rev cont)) with 
                    |(e1, Some e2) -> e2 
                    |_ -> Var x 
                  )
          with
          |Not_found ->  Var x )
|App(t1,t2) -> (match normalize' cont t1 with 
                  |Abs(x, xtype, e1) ->   (subst x t2 e1)
                  |e1 -> App(e1, normalize' cont t2)
                )
|Abs(x ,xtype, t) -> Abs(x, normalize' cont xtype, normalize' (cont@[(x, (xtype, None))]) t)
|Pi(x, a, b) -> Pi(x, normalize' cont a, normalize' (cont@[(x, (a, None))]) b)
|Z ->Z
|S(t) -> S(normalize' cont t)
|Ind(t1,t2,t3,t4) when t4 = Z -> t2
|Ind(p,z,s,S(n)) -> let newp = normalize' cont p in 
                    let newz = normalize' cont z in 
                    let news = normalize' cont s in 
                    let newn = normalize' cont n in
                  (App(App(news,newn),Ind( newp,newz,news,newn)))
|Ind(p,z,s,n) -> let newp = normalize' cont p in 
                    let newz = normalize' cont z in 
                    let news = normalize' cont s in 
                    let newn = normalize' cont n in  
                    (Ind(newp, newz, news, newn))               
|Eq(t1,t2) -> Eq(normalize' cont t1, normalize' cont t2)
|Refl(t1) -> Refl(normalize' cont t1)
|J(p,r,x,y,e) when x = y && (e = Refl x) -> (App(r,x))
|J(p,r,x,y,e) -> J(normalize' cont p, normalize' cont r, normalize' cont x, normalize' cont y, normalize' cont e) 

let rec normalize cont e = 
  let newe = normalize' cont e in
  if newe = e then e else (normalize cont newe)


(* Q 5.7 *)

let rec alpha e1 e2 = match (e1,e2) with 
|Var x, Var y when x=y -> true 
|Type,Type -> true 
|Nat, Nat -> true
|App(t1,t2),App(p1,p2) -> (alpha t1 p1) && (alpha t2 p2)
|Abs(x,xtype,t1),Abs(y, ytype,t2) when x=y-> (alpha xtype ytype) && ( alpha t1 t2 )
|Abs(x,xtype,t1),Abs(y, ytype,t2)  -> let newv = fresh_2 t1 t2 in 
                                                      let t11 = subst x (Var newv) t1 in 
                                                      let t22 = subst y (Var newv) t2 in 
                                                      (alpha xtype ytype) && (alpha t11 t22)
|Pi(x,a,b),Pi(y,c,d) when x=y -> (alpha a c) && (alpha b d)
|Pi(x,a,b),Pi(y,c,d) -> let newv = fresh_2 b d in 
                        let b1 = subst x (Var newv) b in 
                        let d1 = subst y (Var newv) d in 
                        (alpha a c) && (alpha b1 d1)
|Z,Z -> true 
|S(t),S(t1) -> alpha t t1 
|Ind(t1,t2,t3,t4), Ind(p1,p2,p3,p4) -> (alpha t1 p1) && (alpha t2 p2) && (alpha t3 p3) && (alpha t4 p4)
|Eq(t1,t2), Eq(p1,p2) -> alpha t1 p1 &&  alpha t2 p2
|Refl(t),Refl(p) -> (alpha t p)
|J(t1,t2,t3,t4,t5),J(p1,p2,p3,p4,p5) -> (alpha t1 p1) && (alpha t2 p2) && (alpha t3 p3) && (alpha t4 p4) && (alpha t5 p5)
|_ -> false 

(* Q 5.8 *)

let rec conv cont e1 e2 = let e1_n = normalize cont e1 in 
                          let e2_n = normalize cont e2 in 
                          alpha e1_n e2_n

(* Q 5.9 *)

exception Type_error

let rec infer' cont = function 
|Type -> Type
|Var x -> (try match List.assoc x (List.rev cont) with 
                    |(e1, _) -> e1  with Not_found ->  raise Type_error )
|App(t1,t2) -> ( match (infer' cont t1), (infer' cont t2)  with 
                        |Pi(x,a,b),t22 when (conv cont a t22) -> subst x t2 b
                        |_->raise Type_error )
|Abs(x, xt, t) -> Pi(x, normalize cont xt, infer' (cont@[(x,(xt, None))]) t)
|Pi(x, a ,b) -> Type
|Nat -> Type
|Z -> Nat 
|S(t) -> if (infer' cont t = Nat) then Nat else raise Type_error
|Ind(p,z,s,n) -> let tp = infer' cont p in 
                  let tz = infer' cont z in 
                  let ts = infer' cont s in 
                   let tn = infer' cont n in 
                   let a = conv cont tp (Pi("x",Nat,Type) ) in
                   let b = (conv cont tz (App(p,Z))) in
                   let nn = fresh p in 
                   let nx = fresh_2 p (Var nn) in
                   let c = conv cont ts (Pi(nn, Nat, Pi(nx,App(p,Var nn), App(p, S(Var nn)))) ) in 
                   let d = conv cont tn Nat in
                   if a && b && c && d then ( (App(p,n)))  else raise Type_error

|Eq(t1,t2) -> if((infer' cont t1) = (infer' cont t2)) then Type
                  else raise Type_error
|Refl(t1) -> Eq(t1,t1)
|J(p,r,x,y,e) -> let tp = infer' cont p in 
                  let tr = infer' cont r in 
                  let tx = infer' cont x in 
                   let ty = infer' cont y in
                   let  te = infer' cont e in
                   let c = conv cont ty tx in 
                   let newx = fresh_2 tx p in
                   let newy = fresh_2 tx p in
                   let a = conv cont tp (Pi(newx,tx,Pi(newy,tx, Pi("z",Eq(Var newx, Var newy), Type))) ) in
                   let b = conv cont tr (Pi(newx,tx, App(App(App(p,Var newx),Var newx), Refl(Var newx)))) in
                   let d = conv cont te (Eq(x,y)) in
                   if(a && b && c && d) then ( (App(App(App(p,x),y), e)) ) else raise Type_error

let infer cont t = normalize  cont (infer' cont t)
(* Q 5.10 *)

let check cont e2 t = if conv cont (infer cont e2) t then () else raise Type_error

(* Q 5.12  *)



(** Parsing of expressions. *)
let () = Printexc.record_backtrace true
exception Parse_error
let lexer = Genlex.make_lexer ["("; ","; ")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"; "Nat"; "Z"; "S"; "Ind"; "Eq"; "Refl"; "J"]
let of_tk s =
  let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error in
  let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false in
  let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false in
  let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error in
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"] in
  let rec e () = abs ()
  and abs () =
    if peek_kwd s "Pi" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let b = e () in
        Pi (x, a, b)
      )
    else if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let t = e () in
        Abs (x, a, t)
      )
    else
      app ()
  and app () =
    let t = ref (arr ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, base ())
    done;
    !t
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_", t, u)
    else
      t
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Type" -> Type
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "Z" -> Z
    | Genlex.Kwd "S" ->
       let t = base () in
       S t
    | Genlex.Kwd "Ind" ->
       let p = base () in
       let z = base () in
       let ps = base () in
       let n = base () in
       Ind (p, z, ps, n)
    | Genlex.Kwd "Eq" ->
       let t = base () in
       let u = base () in
       Eq (t, u)
    | Genlex.Kwd "Refl" ->
       let t = base () in
       Refl t
    | Genlex.Kwd "J" ->
       let p = base () in
       let r = base () in
       let x = base () in
       let y = base () in
       let e = base () in
       J (p, r, x, y, e)
    | Genlex.Kwd "(" ->
       let t = e () in
       must_kwd s ")";
       t
    | _ -> raise Parse_error
  in
  e ()
let of_string a = of_tk (lexer (Stream.of_string a))

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
         let x, sa = split ':' arg in
         let a = of_string sa in
         check !env a Type;
         env := (x,(a,None)) :: !env;
         print_endline (x^" assumed of type "^to_string a)
      | "define" ->
         let x, st = split '=' arg in
         let t = of_string st in
         let a = infer !env t in
         env := (x,(a,Some t)) :: !env;
         print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
         print_endline (string_of_context !env)
      | "type" ->
         let t = of_string arg in
         let a = infer !env t in
         print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
         let t, a = split '=' arg in
         let t = of_string t in
         let a = of_string a in
         check !env t a;
         print_endline "Ok."
      | "eval" ->
         let t = of_string arg in
         let _ = infer !env t in
         print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | e -> print_endline ("Error: "^Printexc.to_string e) 
  done;
  print_endline "Bye."


(* Q 5.12 *)

(* 
define pred = fun (m : Nat) -> Ind (fun (n : Nat) -> Nat) (Z) (fun (n : Nat) -> fun (q : Nat) -> n )  m

define add = fun (q : Nat) -> fun (m : Nat) -> Ind (fun (n : Nat) -> Nat) (q) (fun (n : Nat) -> fun (nq : Nat) -> (S nq) )  m
*)

(* 5.14 Using the prover *)

(*
define p = fun (x : Nat) -> fun (y : Nat) -> fun (e : Eq x y) -> Eq (S x) (S y)
define r = fun (x : Nat) -> Refl (S x)
define Seq = fun (x : Nat) -> fun (y : Nat) -> fun (e : Eq x y) -> J p r x y e
 *)

 (*
 define addz = fun (n : Nat) -> Refl n
  *)

(*

define p1 = fun (n : Nat) -> Eq (add Z n) n
define s = fun (x : Nat) -> fun (q : (p1 x)) -> Seq (add Z x) x q
define zadd = fun (n : Nat) -> Ind p1 (Refl Z) s n
 *)

 (* Associativity of addition

 define assoc_p = fun (n : Nat) -> fun (m : Nat) -> fun (x : Nat) -> Eq (add (add n m) x) (add n (add m x))
define assoc_add = fun (n : Nat) -> fun (m : Nat) -> fun (q : Nat) -> Ind (assoc_p n m) (Refl (add n m)) (fun (x : Nat) -> fun (w : (assoc_p n m x)) -> Seq (add (add n m) x) (add n (add m x))  w) q
*)

(* Commutativity

 We first prove compativiliy of addition and successor : add (S n) m = S (add n m)

define p2 = fun (n : Nat) -> (fun (x : Nat) -> Eq (add (S n) x) S(add n x) )
define s2 =  fun (n : Nat) -> fun (x : Nat) -> fun (q : p2 n x) -> Seq (add (S n) x) (S (add n x)) q 
define sadd = fun (n : Nat) -> fun (m : Nat) -> Ind (p2 n) (Refl S n) (s2 n) m

And transitivity of equality :

define ptrans = fun (x : Nat) -> fun (y : Nat) -> fun (e : Eq x y) -> (Pi (z : Nat) -> Pi (e : Eq y z) -> Eq x z )
define rtrans = fun (n : Nat) -> fun (z : Nat) -> fun (e : Eq n z) -> e
define trans = fun (n : Nat) -> fun (m : Nat) -> fun (u : Eq n m) -> (J ptrans rtrans n m u)

Then :

define comm_p = fun (n : Nat) -> fun (m : Nat) -> Eq (add m n) (add n m)
define comm_s = fun (n : Nat) -> fun (x : Nat) -> fun (q : (comm_p n x)) -> (trans (add (S x) n) (S (add x n)) (sadd x n) ) (add n (S x)) (Seq (add x n) (add n x) q) 
define comm_add = fun (n : Nat) -> fun (m : Nat) -> Ind (comm_p n) (zadd n) (comm_s n) m
check comm_add = Pi (n : Nat) -> Pi (m : Nat) -> Eq (add m n) (add n m)


  *)


(*
Multiplication :

We first prove compatibility of addition with equality

ddefine add_eq = fun (x : Nat) -> fun (y : Nat) -> fun (a : Nat) -> fun (e : Eq x y) -> Eq (add x a) (add y a)
define add_eq_p = fun (x : Nat) -> fun (y : Nat) -> fun (n : Nat) -> Eq (add x n) (add y n)
define add_eq_s = fun (x : Nat) -> fun (y : Nat) -> fun (n : Nat) -> fun (q : add_eq_p x y n) -> Seq (add x n) (add y n) q
define add_eq = fun (x : Nat) -> fun (y : Nat) -> fun (a : Nat) -> fun (e : Eq x y) -> Ind (add_eq_p x y) e (add_eq_s x y) a


 *)
