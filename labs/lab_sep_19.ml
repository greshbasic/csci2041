type exercise = 
	| Int of int
	| Div of exercise * exercise
	| Add of exercise * exercise

let plus x y = Some (x + y)

let divide x y = Some (x / y)

(* TODO *)
let divide_proper (x: int) (y: int) : int option =
    match y with
    | 0 -> None
    | _ -> match (x,y) with
            | (a, b) -> divide a b

    
let divide_lifted x y = 
    match (x,y) with
    | (Some a, Some b) -> divide_proper a b
    | _ -> None

let plus_lifted x y =
	match (x,y) with
	| (Some a, Some b) -> plus a b
	| _ -> None

let rec eval (e: exercise) : int option = 
	match e with
	| Int i -> (Some i)
	| Add (e1, e2) -> plus_lifted (eval e1) (eval e2)
	| Div (e1, e2) -> divide_lifted (eval e1) (eval e2)

(* TODO *)
let rec string_of_exercise (e: exercise) : string =
        match e with
        | Int i -> string_of_int i
        | Add (e1, e2) -> "(" ^ string_of_exercise e1 ^ " + " ^ string_of_exercise e2 ^ ")"
        | Div (e1, e2) -> "(" ^ string_of_exercise e1 ^ " / " ^ string_of_exercise e2 ^ ")"


(* Tests for plus *)
let test_plus () =
    assert (plus 3 4 = Some 7);
    assert (plus (-1) 1 = Some 0);
    print_endline "All tests for plus passed!"

(* Tests for divide_proper *)
let test_divide_proper () =
    assert (divide_proper 10 5 = Some 2);
    assert (divide_proper 10 0 = None);
    assert (divide_proper (-10) (-5) = Some 2);
    print_endline "All tests for divide_proper passed!"

(* Tests for plus_lifted *)
let test_plus_lifted () =
    assert (plus_lifted (Some 3) (Some 4) = Some 7);
    assert (plus_lifted None (Some 4) = None);
    assert (plus_lifted (Some 3) None = None);
    print_endline "All tests for plus_lifted passed!"

(* Tests for eval *)
let test_eval () =
    assert (eval (Int 5) = Some 5);
    assert (eval (Add (Int 3, Int 4)) = Some 7);
    assert (eval (Div (Int 10, Int 5)) = Some 2);
    assert (eval (Div (Int 10, Int 0)) = None);
    print_endline "All tests for eval passed!"

(* Tests for string_of_exercise *)
let test_string_of_exercise () =
    assert (string_of_exercise (Int 5) = "5");
    assert (string_of_exercise (Add (Int 3, Int 4)) = "(3 + 4)");
    assert (string_of_exercise (Div (Int 10, Int 5)) = "(10 / 5)");
    print_endline "All tests for string_of_exercise passed!"

(* Run all tests *)
let run_all_tests () =
    test_plus ();
    test_divide_proper ();
    test_plus_lifted ();
    test_eval ();
    test_string_of_exercise ();
    print_endline "All tests passed!"

(*  UNCOMMENT THE BELOW LINE TO RUN TESTS *)

let _ = run_all_tests ()

