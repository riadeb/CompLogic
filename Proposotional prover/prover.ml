(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Q 1.1 type **)
type ty =
|Tvar of tvar 
|Arr of ty*ty
|Conj of ty*ty
|Disj of ty*ty
|True
|False
|Nat

(**  Q 1.2 :  lambda_term , Church style **)
type tm =
|Var of var
|App of tm*tm
|Abs of var*ty*tm
|Pair of tm*tm
|PrjL of tm 
|PrjR of tm
|Unit
|Left_inj of tm*ty
|Right_inj of tm*ty
|Case of tm*var*tm*var*tm
|Absurd of tm*ty
|Zero
|Succ of tm 
|Rec of tm*tm*var*var*tm

(**  Q 1.3 **)
let rec string_of_ty = function
|Tvar v -> v 
|Arr (t1,t2) -> "("^(string_of_ty t1) ^" => "^(string_of_ty t2)^")"
|Conj (t1, t2) -> "("^(string_of_ty t1) ^" ∧ "^(string_of_ty t2)^")"
|True -> "⊤"
|Disj (t1, t2) -> "("^(string_of_ty t1) ^" ∨ "^(string_of_ty t2)^")"
|False -> "⊥"
|Nat -> "N"


let rec string_of_tm = function
|Var v -> v
|App(t1,t2) ->  "("^string_of_tm(t1) ^ " " ^ string_of_tm(t2) ^")"
|Abs(x,xtype,t) -> "(fun ("^x^" : "^(string_of_ty xtype)^") -> "^(string_of_tm t)^")"
|Pair(t1,t2) -> "<"^(string_of_tm t1)^" , "^(string_of_tm t2) ^">"
|PrjL(t) -> "(Πι ("^(string_of_tm t) ^"))"
|PrjR(t) -> "(Πr ("^(string_of_tm t) ^"))"
|Unit -> "⊤"
|Left_inj (x, xtype) -> "(Iι ("^(string_of_tm x) ^"))"
|Right_inj (x, xtype) -> "(Ir ("^(string_of_tm x) ^"))"
|Case(t, x , u, y , v) -> "case "^(string_of_tm t)^" of "^( x)^" -> "^(string_of_tm u)^"| "^( y)^" -> "^(string_of_tm v)
|Absurd(t, ty) -> "Absurd( "^(string_of_tm t)^")"
|Zero -> "0"
|Succ(t) -> "Succ("^(string_of_tm t)^")"
|Rec(t1,t2,x,y,t3) -> "rec "^(string_of_tm t1) ^", "^(string_of_tm t2) ^" | "^x^" , "^y^" -> "^(string_of_tm t3)



let () =
    let t = Abs("f",Arr(Tvar "A", Tvar "B"), Abs("x",Tvar "A", App(Var "f", Var "x"))) in 
    assert(string_of_tm t = "(fun (f : (A => B)) -> (fun (x : A) -> (f x)))")

(* Q 1.4 *)

type context = (string * ty) list

exception Type_error


let rec infer_type (cont:context) = function
|Var x -> (try List.assoc x (List.rev cont)  with Not_found -> raise Type_error)
|Abs(x, xtype, t) ->  let newcont = cont@[(x,xtype)] in
                        Arr(xtype, (infer_type newcont t) )
|App(t1,t2) -> 
         ( match infer_type cont t1 with 
                        |Arr(a,b) -> if(check_type cont t2 a) then b else raise Type_error
                        |_ -> raise Type_error 
                         
        )

|Pair(t1,t2) -> Conj ((infer_type cont t1),(infer_type cont t2))
|PrjL t ->  (match infer_type cont t with 
            |Conj(a,b) -> a 
            |_ -> raise Type_error )
|PrjR t ->  (match infer_type cont t with 
            |Conj(a,b) -> b
            |_ -> raise Type_error )       
|Unit -> True
|Left_inj (x, xtype) -> Disj((infer_type cont x), xtype)
|Right_inj (x, xtype) -> Disj(xtype, (infer_type cont x))
|Case(t,x , u,y,v) -> (match infer_type cont t with 
            |Disj(a,b) -> (match infer_type (cont@[(x,a)]) u,infer_type (cont@[(y,b)]) v  with 
                                |y, r when y = r     -> r
                                |_ -> raise Type_error
                                    ) 
            |_ -> raise Type_error )
|Absurd(t, ty) -> (match infer_type cont t with 
            |False -> ty    
            |_ -> raise Type_error )
|Zero -> Nat 
|Succ(t) -> (
        match infer_type cont t with 
        |Nat -> Nat 
        |_ -> raise Type_error
)
|Rec(t1,t2,x,y,t3) -> if infer_type cont t1 <> Nat then raise Type_error 
                      else let c = infer_type cont t2 in 
                      let d = infer_type (cont@[(x,Nat)]@[(y,c)]) t3 in 
                      if d =c then d else raise Type_error
|_ -> raise Type_error
                



and check_type cont t typ = try (infer_type cont t) = typ with Type_error -> false

let terr =
    let t1 = Abs("f",Arr(Tvar "A",Tvar "B"), Abs("g",Arr(Tvar "B", Tvar "C"),Abs("x", Tvar "A", App(Var "g", App(Var "f", Var "x"))) )) in 
    assert(infer_type [] t1 = Arr(Arr(Tvar "A",Tvar "B"), Arr(Arr(Tvar "B",Tvar"C"),Arr(Tvar "A", Tvar "C"))));
    let t2 = Abs("f", Tvar "A", Var "x") in
    let t3 = Abs("f", Tvar "A", Abs("x", Tvar "B", App(Var"f", Var "x"))) in 
    let t4 = Abs("f", Arr(Tvar "A", Tvar "B"), Abs("x", Tvar "B", App(Var "f", Var "x"))) in 
    let err1  = (try  (infer_type [] t2) with 
        |Type_error -> Tvar "A"
        |_ -> raise Not_found ) in 
    let err2  = (try  (infer_type [] t3) with 
        |Type_error -> Tvar "A"
        |_ -> raise Not_found ) in 
    (try  (infer_type [] t4) with 
        |Type_error -> Tvar "A"
        |_ -> raise Not_found )
    
    (* Q 1.5 *)

    (* 
    let check_type cont t typ = try (infer_type cont t) = typ with Type_error -> false 
    *)

    let () =
        let t1 = Abs("x", Tvar "A", Var "x") in 
        let t2 = t1 in 
        let t3 = Var "x" in
        assert((check_type [] t1 (Arr(Tvar "A", Tvar "A"))));
        assert(not (check_type [] t2 (Arr(Tvar "B", Tvar "B")) )) ;
        assert(not (check_type [] t3 (Tvar "A") ));

(* Q 1.6 *)

(* functions modified below *)

(* Q 1.8 *)

(* Constructors and inference rules added below *)

let and_comm = Abs("p", Conj(Tvar "A", Tvar "B"), Pair(PrjR(Var "p"), PrjL(Var "p"))) in 
print_endline (string_of_ty (infer_type [] and_comm));


(* Q 1.9 *)
let truth = Abs("p", Arr(True, Tvar "A"), App(Var "p", Unit)) in 
print_endline (string_of_ty (infer_type [] truth));

(* Q 1.10 *)

(* functions modified below *)

let or_comm = Abs("p", Disj(Tvar "A", Tvar "B"), Case(Var "p",  "x", Right_inj(Var "x", Tvar "B"),  "y", Left_inj(Var "y", Tvar "A")  )  ) in 
print_endline (string_of_ty (infer_type [] or_comm));

(* Q 1.11 *)

(* functions modified below *)

let prove_any = Abs("p", Conj(Tvar "A", Arr(Tvar "A", False)), Absurd(App(PrjR(Var "p"), PrjL(Var "p") ) , Tvar "B")) in 
print_endline (string_of_ty (infer_type [] prove_any));

(* Parser *)


exception Parse_error

let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_";"Nat"]
let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then Arr (a, arr ()) else a
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then Conj (a, prod ()) else a
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then Disj (a, sum ()) else a
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Tvar x
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> True
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "_" -> False
    | Genlex.Kwd "not" ->
       let a = base () in
       Arr (a, False)
    | _ -> raise Parse_error
  in
  ty ()
let tm_of_tk s =
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
  let ty () = ty_of_tk s in
  let rec tm () = app ()
  and app () =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
  and abs () =
    if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x, a, t)
      )
    else if peek_kwd s "case" then
      (
        let t = tm () in
        must_kwd s "of";
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t, x, u, y, v)
      )
    else
      base ()
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Unit
       else
         let t = tm () in
         if peek_kwd s "," then
           let u = tm () in
           must_kwd s ")";
           Pair (t, u)
         else
           (
             must_kwd s ")";
             t
           )
    | Genlex.Kwd "fst" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       PrjL t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       PrjR t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Left_inj (t, b)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Right_inj (t, a)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       Absurd (t, a)
    | _ -> raise Parse_error
  in
  tm ()
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))

(* END Parser *)
let () =
  let l = [
      "A => B";
      "A /\\ B";
      "T";
      "A \\/ B";
      "_";
      "not A"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l

let () =
  let l = [
      "t u";
      "fun (x : A) -> t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l


  (* Q 2 *)

(* Q 2.1 *)
let string_of_ctx cont = String.concat " , " (List.map (fun (a,b) -> a^" : "^string_of_ty b) cont)

(* Q 2.2 *)
let fresh = 
  let x = ref 0 in
  fun () -> let r = !x in 
            x := r+1;
          "x" ^ string_of_int r

type sequent = context * ty

let string_of_seq (cont,t) = string_of_ctx cont ^" |- "^string_of_ty t

let rec prove env a out =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a out in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  output_string out (cmd^" "^arg^"\n");
  match cmd with
  | "intro" ->
     (
       match a with
       | Arr (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b out in
            Abs (x, a, t)
        |Conj(a,b) -> 
          let t1 = prove env a out in
          let t2 = prove env b out in 
          Pair(t1,t2)
        |True -> Unit
        |Nat -> 
          if arg = "0" then Zero 
          else let t = prove env a out in 
          Succ(t)

       | _ ->
          error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" -> 
    let t = tm_of_string arg in (
      match infer_type env t with 
        |Arr(x,y) when y = a -> 
            let u = prove env x out in 
            App(t, u)
        |Disj(x,y) -> 
          let firs_v = fresh() in
          let second_v = fresh() in 
          let u = prove (env@[(firs_v ,x)]) a out in 
          let v = prove (env@[(second_v ,y)]) a out in
          Case(t, firs_v, u,second_v,v)
        |False -> Absurd(t,a)
        |Nat -> let z = prove env a out in 
                 let firs_v = fresh() in
                  let second_v = fresh() in 
                  let s = prove (env@[(firs_v ,Nat)]@[(second_v ,a)]) a out in 
                  Rec(t,z,firs_v,second_v,s)
        |_ -> error "Not the right type"

    )
  | "cut" ->
    let b = ty_of_string arg in 
    let t = prove env (Arr(b,a)) out in 
    let u = prove env b out in 
    App(t,u)
  | "fst" ->
    let x = tm_of_string arg in (
    match infer_type env x with 
    |Conj(t1,t2) when t1 = a -> PrjL(x)
    |_ -> error "Not the right type"
    )
  | "snd" ->
  let x = tm_of_string arg in (
  match infer_type env x with 
  |Conj(t1,t2) when t2 = a -> PrjR(x)
  |_ -> error "Not the right type"
  )
  |"left" ->(
    match a with
    |Disj(x,y) -> 
      let t = prove env x out in 
      Left_inj (t,y)
    |_ -> error "Not proving a disjonction"
  )
  |"right" ->(
    match a with
    |Disj(x,y) -> 
      let t = prove env y out in 
      Right_inj (t,x)
    |_ -> error "Not proving a disjonction"
  )
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Enter filename to save the proof";
  let file_name = input_line stdin in
  let file_out = open_out file_name in
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  output_string file_out (a^"\n");
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a file_out in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."

  (* Q 2.9 *)
(* 
The elim tactic needs to be defined for any term (just like the cut) in order to prove dist.proof
*)

(* Q 3.3 *)

(* pred function : (fun (n : N) -> rec n, 0|x0x1 -> x0) *)
(* addition function : (fun (n : N) -> (fun (m : N) -> rec m, n | x0 , x1 -> Succ(x1)))*)


(* Part 5 : Dependent types *)
