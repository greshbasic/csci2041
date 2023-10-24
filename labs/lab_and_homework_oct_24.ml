
(** A Monoid is an associative operation with an identity element.
   Examples include addition with 0, or multiplication with 1.
   In this signature, the operation is called op, the identity element id **)
module type Monoid = 
sig
	type t
	(** id must be a left identity for op, i.e.
	    [op id x = x]
	    And id must also be a right identity, i.e.
	    [op x id = x] **)
	val id : t
	(* op must be associative, i.e.
	     [op (op x y) z = op x (op y z)] *)
	val op : t -> t -> t
end

(* The plus instance is as in the previous homework: *)

type nat = Zero | S of nat
module Plus = struct
   type t = nat
   let rec plus a b =
     match b with
     | Zero -> a
     | S i -> plus (S a) i 
   let op = plus
   let id = Zero
end

(* The Max instance takes the maximum of two numbers: *)

module Max = struct
   type t = nat
   let rec max a b =
     match (a, b) with
       | (Zero, x) -> x
       | (x, Zero) -> x
       | (S x, S y) -> S (max x y)
   let op = max
   let id = Zero
end

(* The Append instance has 'append' as its operation and the empty list as identity element: *)

module Append = struct
   type t = int list
   let rec append a b =
     match a with
       | [] -> b
       | h::tl -> h::(append tl b)
   let op = append
   let id = []
end

(* This is the lab exercise for October 24th:
   prove that Append satisfies the properties listed in the Monoid signature.
   The following takes care of the type-checking: *)
let _ = (module Append : Monoid)
(* We just need to add proofs that show that:
   - Append.op is associative (proof is in the slides!)

            Case: a = []
                     append (append a b) c
                  = {case}
                     append (append [] b) c
                  = {definition append}
                     append (match [] with | [] -> b | (h::tl) -> h::append tl b) c
                  = {matching pattern}
                     append b c
                  = {matching pattern}
                     match [] with | [] -> append b c
                     | h::tl -> h::append tl (append b c)
                  = {definition append}
                     append [] (append b c)
                  = {case}
                     append a (append b c)

            Case: a = h::t
            Inductive hypothesis’ (IH): append (append tl b) c = append tl (append b c)

                     append (append a b) c
                  = {case}
                     append (append (h :: tl) b) c
                  = {append definition}
                     append (match h :: tl with [] -> b | h :: tl -> h :: append tl b) c
                  = {match fits pattern}
                     append (h :: append tl b) c
                  = {append definition}
                     match (h :: append tl b) with [] -> c | h :: tl2 -> h :: append tl2 c
                  = {match fits pattern}
                     h :: append (append tl b) c
                  = {IH}
                     h :: append tl (append b c)
                  = {match fits pattern}
                     match h :: tl with
                     | [] -> (append b c)
                     | h :: tl -> h :: append tl
                     (append b c)
                  = {append definition}
                     append (h :: tl) (append b c)
                  = {case}
                     append a (append b c)



   - Append.id is a left identity (this one is easy) b
               Prove: append id x = x

                     append id x
                  = { case }
                     append [] h::t
                  = { append def }
                    let rec append a b =
                        match [] with
                        | [] -> b
                        | h::tl -> h::(append tl b)
                  = { apply match }
                     h::t
                  = { case }
                     x

   - Append.id is a right identity (this one is a straightforward induction on lists)

               Prove: append x id = x

               Base case: x = []

                     append x id
                  = { case }
                     append [] []
                  = { append def }
                    let rec append a b =
                        match [] with
                        | [] -> b
                        | h::tl -> h::(append tl b)
                  = { apply match }
                     []
                  = { case }
                     x

               Case: x = h::tl
               IH: append tl id = tl

                     append x id
                  = { case }
                     append h::tl []
                  = { append def }
                    let rec append a b =
                        match tl with
                        | [] -> b
                        | h::tl -> h::(append tl b)
                  = { apply match }
                     h::(append tl [])
                  = { IH }
                     h::tl
                  = { case }
                     x

   *)
               
let _ = (module Plus : Monoid)
 (* Proofs that this is true were in the previous homework,
    you don't have to repeat them in this homework.
    (On October 24th, I will include them myself.)
    *)

let _ = (module Max : Monoid) (* Proofs for this you have to write still *)
(*
   Prove: Max.op Max.id a = a

            Base Case: a = 0

                     Max.op Max.id a
                  = { case }
                     Max.op Zero Zero
                  = { Max definition }
                     let rec max a b =
                        match (Zero, Zero) with
                        | (Zero, x) -> x
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                  = { apply match }
                     Zero
                  = { case }
                        a
            
            Case: a = S n
            IH: append Max.id n = n ( why didn't i have to use an IH at all?) 
            
                     Max.op Max.id a
                  = { case }
                        Max.op Zero (S n)
                  = { Max definition }
                     let rec max a b =
                        match (Zero, S n) with
                        | (Zero, x) -> x
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                  = { apply match }
                        S n
                  = { case }
                        a


   Prove: Max.op a Max.id = a
            Base case: a = Zero
                        
                     Max.op a Max.id
                  = { case }
                        Max.op Zero Zero
                  = { Max definition }
                     let rec max a b =
                        match (Zero, Zero) with
                        | (Zero, x) -> x
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                  = { apply match }
                     Zero
                  = { case }
                     a   
                           
            Case: a = S n
            IH: append n Max.id = n ( why didn't i have to use an IH at all?)                

                        Max.op a Max.id
                     = { case }
                        Max.op (S n) Zero
                     = { Max definition }
                        let rec max a b =
                           match (S n, Zero) with
                           | (Zero, x) -> x
                           | (x, Zero) -> x
                           | (S x, S y) -> S (max x y)
                     = { apply match }
                           S n
                     = { case }                    
                           a
            
*)
(* On associativity of Max.op:            
    You will need some case distinction inside your inductive step.
    Consider these cases in the inductive step:
     - b = Zero
     - c = Zero
     - b = S b' and c = S c'
    (Why are these the only cases you need to consider?) *)

module Combine (M : Monoid) = struct
   let rec combine_r lst =
      match lst with
      | []   -> M.id
      | h :: t -> M.op h (combine_r t)

   let rec combine_l acc lst =
      match lst with
      | []   -> acc
      | h :: t -> (combine_l (M.op acc h) t)
end

(* To prove that [combine_r lst = combine_l M.id lst], you need to prove a stronger lemma.
   The lemma is that [M.op a (combine_r lst) = combine_l a lst] for any a.
   You can prove this by induction on lst.
   Using this lemma, you can prove the original theorem by setting a = M.id.
   *)

(*
Testing associativity and identity element properties:
*)
module type MonoidWithValues =
sig
    include Monoid
    val values : (t*t*t)
end

module AppendV = struct
   include Append
   let values = ([2;3;4], [5;6], [7;8;9])
end
module MaxV = struct
   include Max
   let values = (S (S Zero), S (S (S Zero)), S (S (S (S Zero))))
end
module PlusV = struct
   include Plus
   let values = (S (S Zero), S (S (S Zero)), S (S (S (S Zero))))
end

let is_assoc op (v1,v2,v3)
  = assert (op (op v1 v2) v3 = op v1 (op v2 v3));
    assert (op (op v1 v3) v2 = op v1 (op v3 v2));
    assert (op (op v1 v2) v2 = op v1 (op v2 v2));
    assert (op (op v1 v3) v3 = op v1 (op v3 v3));
    assert (op (op v2 v1) v3 = op v2 (op v1 v3));
    assert (op (op v2 v3) v1 = op v2 (op v3 v1));
    assert (op (op v3 v1) v2 = op v3 (op v1 v2));
    assert (op (op v3 v2) v1 = op v3 (op v2 v1))

let is_id op idt (v1,v2,v3)
  = assert (op idt v1 = v1);
    assert (op idt v2 = v2);
    assert (op idt v3 = v3);
    assert (op v1 idt = v1);
    assert (op v2 idt = v2);
    assert (op v3 idt = v3)

let test_monoidV (module M : MonoidWithValues) =
   is_assoc M.op M.values;
   is_id M.op M.id M.values

let _ = test_monoidV (module AppendV)
let _ = test_monoidV (module MaxV)
let _ = test_monoidV (module PlusV)

(*
Testing combine functions:
*)
let test_combine (module M : MonoidWithValues) =
   let module C = Combine(M) in
   let (v1,v2,v3) = M.values in
   assert (C.combine_r [v1;v2;v3] = C.combine_l M.id [v1;v2;v3]);
   assert (C.combine_r [v3;v2;v3] = C.combine_l M.id [v3;v2;v3]);
   assert (C.combine_r [v2;v2;v1] = C.combine_l M.id [v2;v2;v1]);
   assert (C.combine_r [v1;v2;v3] = M.op (M.op v1 v2) v3);
   assert (C.combine_l M.id [v1;v2;v3] = M.op (M.op v1 v2) v3)

let _ = test_combine (module AppendV)
let _ = test_combine (module MaxV)
let _ = test_combine (module PlusV)
