  (*
    Function Programming

    Example "sumFrom":
    - what we have: expressions, definitions, recursion, integers (types), comments
    - what we dont have: (re)assignment, state

  *)
    let rec sumFrom s e (* sum from s(tart) to e(nd)*)
      = s + (if s = e then 0 else sumFrom (s+1) e)
    let sumAll = sumFrom 1 100

  (*
    PYTHON VERSION:
    def sumFrom(s, e):
      sum = s
      if s == e:
        return s
      else:
        return sum + sumFrom(s+1, e)
    sumAll = sumFrom(1,3)
  *)

  (*
    Examples of expressions:
    - let foo = 1
    - let rec foo = 1
    - foo = 1
    - 1
    - let foo = 1 in bar
  *)

  (*
      utop is a fancy calculator. We can:
      - enter expressions and see their value
      - add definitons (overriding old ones)
      - add definitions from a file
      - looking for "Welcome to utop version 2.9.2" LOL
      - > utop #
      ocamlc is used to compile programs
      - pass filenames as arguments
      - run "./a.out" as your compiled program
      - this requires a program that "does" stuff
  *)

  (*
     
  Erroneous:
  utop # let rec sumFrom s e
    = if s then 0 else (sumFrom (s+1) e);;
    ^^^^^ this is going to error out, by having s initially set in the if statement,
    ocaml is led to believe it is a boolean, not an integer

  Correct:
  utop # let rec sumFrom (s: int) (e:int)
  = if s then 0 else (sumFrom (s+1) e) + 1;;

  Erroneous:
  utop # let sumFrom s e 
    = s + (if s = e then 0
        else sumFrom (s+1) e
  
  Correct:
  utop # let sumFrom s e 
    = s + (if s = e then 0
        else sumFrom (s+1) e
  *)

> let x = 3;;
val x : int = 3
> let x = x + 1;;
val x : int = 4
> let f n = x + n;; (* this is referring to the old x, the x = 3 *)
val f : int -> int = <fun>
> let x = x + 1;;
val x : int = 4 (* x + 1 -> 3 + 1 -> 4 *)
> f 0;;
- int = 4 (* x + 0 -> 4 + 0 -> 4 *)


  


