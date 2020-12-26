type prog =
  |Bool of bool
  |Int of int
  |Add of prog*prog
  |Lt of prog*prog
  |If of prog*prog*prog
  |Prod of prog*prog
           
         
   

let rec reduce = function
  |Add(Int n1, Int n2) -> Some (Int(n1 + n2))
  |Bool _  -> None
  |Int _  -> None
  |Add(p1,  p2) -> ( match reduce p1 with
    |Some p1' -> Some(Add(p1', p2))
    |None -> ( match reduce p2 with
      |Some p2' -> Some(Add(p1, p2'))
      |None -> None) )
    
  |Lt (Int n1, Int n2) -> Some (Bool (n1 < n2))
  |Lt ( p1, p2) -> (match reduce p1 with
      |Some p1' -> Some(Lt(p1',p2))
      |None -> (match reduce p2 with
          |Some p2'-> Some(Lt(p1,p2'))
          |None -> None)

    )
  |If (Bool(true),p1,p2) -> Some(p1)
  |If (Bool(false),p1,p2)-> Some(p2)
  |If ( p1, p2, p3) ->( match reduce(p1) with
    | Some p1' -> Some(If(p1',p2,p3))
    |None -> None)
  |Prod(p1,p2) -> (match reduce p1 with
      | Some p1' -> Some(Prod(p1', p2))
      |None -> (match reduce p2 with
        | Some p2' -> Some(Prod(p1, p2'))
        | None -> None)
    )

let rec normalize p = match reduce p with
  |Some p1 -> normalize(p1)
  |None  -> p

type typ =
  |TInt
  |TBool
  |TProd of typ*typ
  |TUnit
            
            

exception Type_error

let rec  infer = function
  |Int(n1) -> TInt
  |Bool _ -> TBool
  |Add(Int n1, Int n2) -> TInt
  | Add(p1, p2) -> (match (infer p1, infer p2)  with
      |(TInt, TInt) -> TInt
      | (t1, t2) -> raise Type_error)
   | Lt(p1, p2) -> (match (infer p1, infer p2)  with
      |(TInt, TInt) -> TBool
      | (t1, t2) -> raise Type_error)
   | If(p1, p2, p3) -> (match (infer p1, infer p2, infer p3) with
       |(TBool, TInt, TInt) -> TInt
         | (TBool, TBool, TBool) -> TBool
        | (t1,t2,t3) -> raise Type_error
     )
  |Prod(p1,p2) -> TProd(infer p1,infer p2)

let projection_f  = function
  |Prod(p1, p2) -> Some (p1)
  |_ -> None

let projection_s  = function
  |Prod(p1, p2) -> Some (p2)
  |_ -> None
     
let typable p =
  try match infer p with _ -> true
  with Type_error -> false

let exp1 = If(Lt(Add(Int(1), Add(Int(2),Int(3))),Int(4)), Bool(false), Int(5))

let exp2 = If(Lt(Add(Int(1), Add(Int(2),Int(3))),Int(4)), Int(4), Int(5))

let exp3  = If(Bool(true), Bool(false), Int(5))
    



    
                         
                            
                                
                                
            

    |And(p1,p2) -> try match free_var p1 with |v -> v 
                    with Not_found ->  try  match free_var p2 with |v -> v 
          with Not_found -> raise Not_found
                              
     |Or(p1,p2) -> try (  match free_var p1 with |v -> v )
                    with Not_found ->  try (
                                             match free_var p2 with |v -> v )
                                        with Not_found -> raise Not_found