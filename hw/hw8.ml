let is_some x = match x with
  | Some _ -> true
  | _ -> false

let rec get_somes xs = match xs with
  | [] -> []
  | Some x :: xs -> x :: get_somes xs
  | None :: xs -> get_somes xs

let rec length lst = match lst with
  | [] -> 0
  | _::xs -> 1 + length xs

module type OptionFunction = sig
  type input
  type output
  val fn : input -> output option
  (** The domain fn should predict whether it yields Some or not.
      That is: it should satisfy the following:
      [domain x = is_some (fn x)]
      (The above would be a valid implementation of domain,
       but there might be a more efficient implementation) **)
  val domain : input -> bool
end

(** Finding the max integer, returns None if no such number exists **)
module FindMax = struct
  type input = int list
  type output = int
  (* Note: this operation is O(n) in the input *)
  let rec fn lst = match lst with
    | [] -> None
    | x::xs -> (match fn xs with
                | None -> Some x
                | Some v -> Some (if x > v then x else v))
  (* Note: this operation is O(1) in the input *)
  let domain lst = match lst with
    | [] -> false
    | _ -> true
end

module SolveList(F : OptionFunction) = struct
  let rec solve lst = match lst with
    | [] -> []
    | x::xs -> (match F.fn x with
                | None -> solve xs
                | Some v -> v :: solve xs)
  let rec filter lst = match lst with
    | [] -> []
    | x::xs -> if F.domain x
               then x :: filter xs
               else filter xs
  (** just apply the function, leaving the None in place **)
  let rec map lst = match lst with
    | [] -> []
    | x::xs -> F.fn x :: map xs
end

(* 
   P1. prove that FindMax satisfies the invariants of OptionFunction
       (uses induction on the list)

       In this problem we will be referring to FindMax.domain and FindMax.fn as domain and fn respectively

      Prove: domain x = is_some (fn x)
      Base case: lst = []

                      domain x
                    = { case }
                      domain []
                    = { domain definition }
                      match [] with
                      | [] -> false
                      | _ -> true
                    = { apply match }
                      false
                    = { is_some definition }
                      match [] with
                      | Some _ -> true
                      | _ -> false
                    = { reverse match }
                      is_some (None)
                    = { fn definition }
                      match [] with
                      | [] -> None
                      | x::xs -> (match fn xs with
                                  | None -> Some x
                                  | Some v -> Some (if x > v then x else v))
                    = { reverse match }
                      is_some (fn [])
                    = { case }
                      is_some (fn x)

                  IS: lst = h::t
                  IH: domain t = is_some (fn t)

                      domain x
                    = { case }
                      domain h::t
                    = { domain definition }
                      match h::t with
                      | [] -> false
                      | _ -> true
                    = { apply match }
                      true
                    = { is_some definition }
                      match [] with
                      | Some _ -> true
                      | _ -> false
                    = { reverse match }
                      is_some (Some ())

                    = { fn definition }

                      match h::t with
                      | [] -> None
                      | x::xs -> (match fn t with
                                  | None -> Some x
                                  | Some v -> Some (if x > v then x else v))
                    = { reverse match }
                      is_some (fn h::t)
                    = { case }
                      is_some (fn x)
                    






   P2. prove that get_somes (map lst) = solve lst
       (induction on the list, doesn't require properties of OptionFunction)

                    Base case: lst = []

                      get_somes (map lst)
                    = { case }
                      get_somes (map [])
                    = { map definition }
                      match [] with
                      | [] -> []
                      | x::xs -> F.fn x :: map xs
                    = { apply match }
                      []
                    = { solve definition }
                      match [] with
                      | [] -> []
                      | x::xs -> (match F.fn x with
                                  | None -> solve xs
                                  | Some v -> v :: solve xs)
                    = { reverse match }
                      solve []
                    = { case }
                      solve lst

                    IS: lst = h::t
                    IH: get_somes (map t) = solve t

                      get_somes (map lst)
                    = { case }
                      get_somes (map h::t)
                    = { map definition }
                      match h::t with
                      | [] -> []
                      | x::xs -> F.fn x :: map xs
                    = { apply match }
                      get_somes (F.fn h :: map t)
                    
                      F.fn h :: (get_somes (map t))
                    = { IH }
                      F.fn h :: solve t
                    = { solve definition }
                      match h::t with
                      | [] -> []
                      | x::xs -> (match F.fn h with
                                    | None -> solve xs
                                    | Some v -> v :: solve xs)
                    = { reverse match }
                      solve h::t
                    = { case }
                      solve lst


   P3. prove that solve (filter lst) = solve lst
       (induction on the list, requires properties of OptionFunction)




                    Base case: lst = []


                      solve (filter lst)
                    = { case }
                      solve (filter [])
                    = { filter definition }
                      match [] with
                      | [] -> []
                      | x::xs -> if F.domain x
                                then x :: filter xs
                                else filter xs
                    = { apply match }
                      []
                    = { solve definition }
                      match [] with
                      | [] -> []
                      | x::xs -> (match F.fn h with
                                    | None -> solve xs
                                    | Some v -> v :: solve xs)
                    = { reverse match }
                      solve []
                    = { case }
                      solve lst


      IS: lst = h::t
      IH: solve (filter t) = solve t

                      solve (filter lst)
                    = { case }
                      solve (filter h::t)
                    = { filter definition }
                      match h::t with
                      | [] -> []
                      | x::xs -> if F.domain h
                                then x :: filter xs
                                else filter xs
                    = { apply match }
                      solve (h :: filter t)

                      
                    = { solve definition }              
                      match h::t with
                      | [] -> []
                      | x::xs -> (match F.fn h with
                                    | None -> solve xs
                                    | Some v -> v :: solve xs)              
                    = { reverse match }
                      solve h::t            
                    = { case }                
                      solve lst

   P4. prove that length (solve lst) = length (filter lst)
       (induction on the list,
        either requires properties of OptionFunction or the use of P3,
        doesn't require properties of 0, 1 and +)
                              
        Base case: lst = []

                    length (solve lst)
                  = { case }
                    length (solve [])
                  = { solve definition }
                    match [] with
                    | [] -> []
                    | x::xs -> (match F.fn h with
                                  | None -> solve xs
                                  | Some v -> v :: solve xs)
                  = { apply match }
                    length []
                  = { filter definition}
                    match [] with
                    | [] -> []
                    | x::xs -> if F.domain h
                              then x :: filter xs
                              else filter xs
                  = { reverse match }
                    length (filter [])
                  = { case }
                    length (filter lst)



        IS: lst = h::t
        IH: length (solve t) = length (filter lst)                    

                    length (solve lst)
                  = { case }
                    length (solve h::t)
                  = { solve definition }
                    match h::t with
                    | [] -> []
                    | x::xs -> (match F.fn h with
                                  | None -> solve t
                                  | Some v -> v :: solve t)
                  = { apply match }
                    length ((match F.fn h with
                                  | None -> solve xs
                                  | Some v -> v :: solve xs))
                  = { fn definition }
                    match h::[] with
                    | [] -> None
                    | x::xs -> (match fn [] with
                                | None -> Some h
                                | Some v -> Some (if x > v then x else v))
                  = { apply match }
                    length ((match Some h with
                                | None -> solve []
                                | Some v -> v :: solve []))
                  = { apply match }
                    length (h :: solve t)

                  = { ??? }

                    length (h :: filter t )
                  = { filter definition }
                    match h::t with
                    | [] -> []
                    | x::xs -> if F.domain h
                              then h :: filter t
                              else filter 
                  = { reverse match }
                    length (filter h::t)
                  = { case }
                    length (filter lst)


   *)               