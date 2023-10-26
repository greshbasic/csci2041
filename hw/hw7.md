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
```

let _ = (module Max : Monoid) (* Proofs for this you have to write still *)
(*
   Prove: Max.op Max.id a = a (P1)

            Base Case: a = 0

                     Max.op Max.id a
                  = { case }
                     Max.op Zero Zero
                  = { Max definition }
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

    Prove: Max.op a (Max.op b c) = Max.op (Max.op a b) c (P3)

         Base case: a = Zero

                     Max.op a (Max.op b c)
                 = { case }
                     Max.op Zero (Max.op b c)
                  = { Max definition }
                     match (Zero, (Max.op b c)) with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (max x y)
                  = { apply match }
                     Max.op b c
                  = { Max definition }
                     match (Zero, b) with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (max x y)
                  = { reverse match }
                     Max.op (Max.op Zero b) c
                  = { case }
                     Max.op (Max.op a b) c

         Inductive Step: a = S a'
         Inductive Hypthesis: Max.op a' (Max.op b' c') = Max.op (Max.op a' b') c'


            Case: b = Zero

                        Max.op a (Max.op b c)
                     = { case }
                        Max.op (S a') (Max.op Zero (S c'))
                     = { Max definition }
                        match (Zero, S c') with
                        | (Zero, x) -> x 
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                     = { apply match }
                        Max.op (S a') (S c')
                     = { Max definition }
                        match (S a', Zero) with
                        | (Zero, x) -> x 
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                     = { reverse match }
                        Max.op (Max.op (S a') Zero) (S c')
                     = { case }
                        Max.op (Max.op a b) c


        Case: c = Zero

                        Max.op a (Max.op b c)
                     = { case }
                        Max.op (S a') (Max.op (S b') Zero)
                     = { Max definition }
                        match (S b', Zero) with
                        | (Zero, x) -> x 
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                     = { apply match }
                        Max.op (S a') (S b')
                     = { Max defintion }
                        match ((Max.op (S a') (S b')), Zero) with
                        | (Zero, x) -> x 
                        | (x, Zero) -> x
                        | (S x, S y) -> S (max x y)
                    = { reverse match }
                        Max.op (Max.op (S a') (S b')) Zero
                    = { case }
                        Max.op (Max.op a b) c


        Case: b = S b' and c = S c'

                     Max.op a (Max.op b c)
                  = { case }
                     Max.op (S a') (Max.op (S b') (S c')) 
                  = { Max definition }
                     match (S b', S c') with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (max x y)
                  = { apply match }
                     Max.op (S a') (S (Max.op b' c'))
                  = { Max definition }
                     match (S a', S (max b' c')) with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (max x y)
                  = { apply match }
                     S (Max.op a' (Max.op b' c'))
                  = { IH }
                     S (Max.op (Max.op a' b') c')
                  = { Max definition }
                     match (S (Max.op a' b'), S c') with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (max x y)
                  = { reverse match }
                     Max.op (S (Max.op a' b')) (S c')
                  = { Max definition }
                     match (S a', S b') with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (max x y)
                  = { reverse match }
                     Max.op (Max.op (S a') (S b')) (S c')
                  = { case }
                     Max.op (Max.op a b) c 

-----------------------------------------------------------------------------------------------------------------------------------

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

      Prove combine_r lst = combine_l M.id lst (P4)
      (* 
      To prove this, you will have to do induction for a slightly stronger property instead (and then use it). The property you'll use is: 
      M.op a (combine_r lst) = combine_l a lst. The properties about M.op and M.id you are allowed to use are written in the signature (so don't use that M.id = Zero, say; the proofs you did during lab show that that's not even necessarily true).
      *)


      Base case: a = []

            M.op a (combine_r lst)
         = { case }
            M.op [] (combine_r (h::t))
         = { combine_r definition }
            match h::t with
            | []   -> M.id
            | h :: t -> M.op h (combine_r t)
         = { apply match }
            M.op [] (M.op h (combine_r t))

          
         