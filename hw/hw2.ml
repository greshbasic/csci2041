type exercise = 
| Int of int
| Mult of exercise * int
| Plus of exercise * int

let exercise_one = (Mult (Plus (Plus (Mult (Int 3, 15), 0), 2), 1))
let exercise_two = Mult (Plus (Mult (Plus (Int 0, 4), 1), 0), 6)
let exercise_three = (Int 64)

let rec solution (prob : exercise) :  int =
        raise (Failure "This function is not implemented")

let rec string_of_exercise (prob : exercise) : string =
        raise (Failure "This function is not implemented")

let string_of_solution (prob : exercise) : string =
        raise (Failure "This function is not implemented")

let rec from_random  (nums : int list) (signs : bool list) : exercise =
        raise (Failure "This function is not implemented")

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
