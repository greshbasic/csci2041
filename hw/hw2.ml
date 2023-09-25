type exercise = 
| Int of int
| Mult of exercise * int
| Plus of exercise * int

let exercise_one = (Mult (Plus (Plus (Mult (Int 3, 15), 0), 2), 1))
let exercise_two = Mult (Plus (Mult (Plus (Int 0, 4), 1), 0), 6)
let exercise_three = (Int 64)


let add x y = x + y
let multiply x y = (x * y)

let rec solution (prob : exercise) :  int =
        match prob with
        | Int i -> i
        | Mult (x,y) -> multiply (solution x) y
        | Plus (x,y) -> add (solution x) y

let rec string_of_exercise (prob : exercise) : string =
        match prob with
        | Int i -> string_of_int i
        | Mult (x,y) -> (string_of_exercise x) ^ " * " ^ (string_of_int y) ^ " -> " ^ "... "
        | Plus (x,y) -> (string_of_exercise x) ^ " + " ^ (string_of_int y) ^ " -> " ^ "... "

let rec string_of_solution (prob : exercise) : string =
        match prob with
        | Int i -> string_of_int i
        | Mult (x,y) -> (string_of_solution x) ^ " * " ^ (string_of_int y) ^ " -> " ^ string_of_int (solution prob)
        | Plus (x,y) -> (string_of_solution x) ^ " + " ^ (string_of_int y) ^ " -> " ^ string_of_int (solution prob)

let rec from_random  (nums : int list) (signs : bool list) : exercise =
        match (nums, signs) with
        | ([],[]) -> Int 0
        | ([], _) -> Int 0
        | (nh::nt, []) -> Int nh
        | (nh::nt, sh::st) -> match sh with
                             | true -> Mult ((from_random (nt)(st)), nh) 
                             | false -> Plus ((from_random (nt)(st)), nh)

let rec filterNonTrivial (prob : exercise) : exercise = 
        raise (Failure "This function is not implemented")

let rec splitOnMultZero (prob : exercise) : (exercise * exercise) option =
        raise (Failure "This function is not implemented")

let rec keepSplitting (prob : exercise) : exercise list =
        raise (Failure "This function is not implemented")

let rec printExercise (probs : exercise list) : unit =
  match probs with
  | h :: tl -> print_string ((string_of_exercise h)^"\n"^(string_of_solution h)^"\n\n"); printExercise tl
  | [] -> ()

let rec genProblems (nums : int list) (signs : bool list) : unit =
  (printExercise (keepSplitting (filterNonTrivial (from_random nums signs))))
