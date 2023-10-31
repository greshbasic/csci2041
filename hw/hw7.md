

let _ = (module Max : Monoid) (* Proofs for this you have to write still *)
(*
   Prove: Max.op Max.id a = a (P1)

            Case: a = 0

                     Max.op Max.id a
                  = { case }
                     Max.op Zero Zero
                  = { Max definition }
                     match (Zero, Zero) with
                     | (Zero, x) -> Zero
                     | (x, Zero) -> Zero
                     | (S x, S y) -> S (Max.op x y)
                  = { apply match }
                     Zero
                  = { case }
                        a
            
            Case: a = S n
            
                     Max.op Max.id a
                  = { case }
                        Max.op Zero (S n)
                  = { Max definition }
                     match (Zero, S n) with
                     | (Zero, x) -> S n
                     | (x, Zero) -> x
                     | (S x, S y) -> S (Max.op x y)
                  = { apply match }
                        S n
                  = { case }
                        a


   Prove: Max.op a Max.id = a (P2)

            case: a = Zero
                        
                     Max.op a Max.id
                  = { case }
                        Max.op Zero Zero
                  = { Max definition }
                     match (Zero, Zero) with
                     | (Zero, x) -> Zero
                     | (x, Zero) -> Zero
                     | (S x, S y) -> S (Max.op x y)
                  = { apply match }
                     Zero
                  = { case }
                     a   
                           
            Case: a = S n           

                     Max.op a Max.id
                  = { case }
                     Max.op (S n) Zero
                  = { Max definition }
                     match (S n, Zero) with
                     | (Zero, x) -> x 
                     | (x, Zero) -> S n
                     | (S x, S y) -> S (Max.op x y)
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
                     | (Zero, x) -> (Max.op b c)
                     | (x, Zero) -> x
                     | (S x, S y) -> S (Max.op x y)
                  = { apply match }
                     Max.op b c
                  = { Max definition }
                     match (Zero, b) with
                     | (Zero, x) -> b
                     | (x, Zero) -> x
                     | (S x, S y) -> S (Max.op x y)
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
                        | (Zero, x) -> S c'
                        | (x, Zero) -> x
                        | (S x, S y) -> S (Max.op x y)
                     = { apply match }
                        Max.op (S a') (S c')
                     = { Max definition }
                        match (S a', Zero) with
                        | (Zero, x) -> x 
                        | (x, Zero) -> S a'
                        | (S x, S y) -> S (Max.op x y)
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
                        | (x, Zero) -> S b'
                        | (S x, S y) -> S (Max.op x y)
                     = { apply match }
                        Max.op (S a') (S b')
                     = { Max defintion }
                        match ((Max.op (S a') (S b')), Zero) with
                        | (Zero, x) -> x 
                        | (x, Zero) -> Max.op (S a') (S b')
                        | (S x, S y) -> S (Max.op x y)
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
                     | (S x, S y) -> S (Max.op b' c')
                  = { apply match }
                     Max.op (S a') (S (Max.op b' c'))
                  = { Max definition }
                     match (S a', S (Max.op b' c')) with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (m y)
                  = { apply match }
                     S (Max.op a' (Max.op b' c'))
                  = { IH }
                     S (Max.op (Max.op a' b') c')
                  = { Max definition }
                     match (S (Max.op a' b'), S c') with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (Max.op (Max.op a' b') c')
                  = { reverse match }
                     Max.op (S (Max.op a' b')) (S c')
                  = { Max definition }
                     match (S a', S b') with
                     | (Zero, x) -> x 
                     | (x, Zero) -> x
                     | (S x, S y) -> S (Max.op a' b')
                  = { reverse match }
                     Max.op (Max.op (S a') (S b')) (S c')
                  = { case }
                     Max.op (Max.op a b) c 

-----------------------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------------------

      Prove combine_r lst = combine_l M.id lst (P4)

         Base case: lst = []

               combine_r lst 
            = { case }
               combine_r []
            = { combine_r definition }
               match [] with
               | []   -> M.id
               | h :: t -> M.op h (combine_r t)
            = { apply match }
               M.id
            = { combine_l definition }
               match [] with
               | []   -> M.id
               | h :: t -> (combine_l (M.op acc h) t)
            = { reverse match }
               combine_l M.id []
            = { case }
               combine_l M.id lst

         Inductive step: lst = h::t
         Inductive Hypothesis: combine_r t = combine_l M.id t

               combine_r lst
            = { case }
               combine_r h::t
            = { combine_r definition }
               match h::t with
               | []   -> M.id
               | h :: t -> M.op h (combine_r t)
            = { apply match }
               M.op h (combine_r t)
            = { LEMMA: M.op a (combine_r lst) = combine_l a lst }
               combine_l h t
            = { right identity }
               combine_l (M.op M.id h) t
            = { combine_l definition }
               match h::t with
               | []   -> h
               | h :: t -> (combine_l (M.op acc h) t)
            = { reverse match }
               combine_l M.id h::t
            = { case }
               combine_l M.id lst


      Prove M.op a (combine_r lst) = combine_l a lst:
         
         Base case: lst = []

               M.op a (combine_r lst)
            = { case }
               M.op a (combine_r [])
            = { combine_r definition }
               match [] with
               | []   -> M.op a (M.id)
               | h :: t -> M.op h (combine_r t)
            = { apply match }
               M.op a M.id
            = { right identity }
               a
            = { combine_l definition }
               match [] with
               | []   -> a
               | h :: t -> (combine_l (M.op a h) t)
            = { reverse match }
               combine_l a []
            = { case }
               combine_l a lst

         Inductive step: lst = h::t
         Inductive Hypothesis: M.op a (combine_r t) = combine_l a t

               M.op a (combine_r lst)
            = { case }
               M.op a (combine_r h::t)
            = { combine_r definition }
               match h::t with
               | []   -> M.op a (M.id)
               | h :: t -> M.op a (M.op h (combine_r t))
            = { apply match }
               M.op a (M.op h (combine_r t))
            = { associative property }
               M.op (M.op a h) (combine_r t)
            = { IH }
               combine_l (M.op a h) t
            = { combine_l definition }
               match h::t with
               | []   -> (M.op a h)
               | h :: t -> (combine_l (M.op a h) t)
            = { reverse match }
               combine_l a h::t
            = { case }
               combine_l a lst
