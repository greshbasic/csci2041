```ocaml
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

type nat = Zero | S of nat

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
```

let _ = (module Max : Monoid) (* Proofs for this you have to write still *)
(*
   Prove: Max.op Max.id a = a (P1)

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


   Prove: Max.op a Max.id = a (P2)
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

    Prove: Max.op a (Max.op b c) = Max.op (Max.op a b) c

    Base Case: c = Zero (b = S m, a = S n)

                        Max.op a (Max.op b c)
                    = { case }
                        Max.op (S n) (Max.op (S m) Zero)
                    = { Max definition }
                        let rec max a b =
                           match (S m, Zero) with
                           | (Zero, x) -> x 
                           | (x, Zero) -> x
                           | (S x, S y) -> S (max x y)
                    = { apply match }
                        Max.op (S n) (S m)
                    = { apply match } 
                        let rec max a b =
                           match ((Max.op (S n) (S m)), Zero) with
                           | (Zero, x) -> x 
                           | (x, Zero) -> x
                           | (S x, S y) -> S (max x y)
                    = { Max definition }
                        Max.op (Max.op (S n) (S m)) Zero
                    = { case }
                        Max.op (Max.op a b) c