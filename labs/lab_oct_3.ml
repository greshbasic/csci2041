(* Monad Definitions *)

let ( >>= ) (opt: 'a option) (f: ('a -> 'b option)) : 'b option =
    match opt with
    | Some x -> f x
    | None -> None

(* only uncomment the following if your OCaml version is 4.08 or greater 
	let ( let* ) = ( >>= ) 
*)

let return x = Some x

let one = return 1
let two = return 2
let three = return 3
let four = return 4
let five = return 5

let plus_proper x y = 
    let s = x + y in  
    match (x >= 0, y >= 0, s >= 0) with  
    | (true, true, true)
    | (false, false, false)
    | (true, false, _)
    | (false, true, _) -> Some s  
    | (_, _, _) -> None

let divide_proper x y =
    match x, y with
    | _ when x = min_int && y = (-1) -> None
    | _, 0 -> None
    | _ -> Some (x / y)

let double x = plus_proper x x  

(* Basic multiplication - may not handle overflows. *)
let times x y = return (x * y)

(* Challenge: Implement 'times' using iterated addition to guard against overflows. 
   Note: Faster methods exist beyond simple repeated addition. *)
let times_proper x y = 
    (* Placeholder using the basic multiplication. Update if attempting the challenge. *)
    times x y

let square x = times x x

let plus1 x = plus_proper x 1

let halve x = divide_proper x 2

let negate x = divide_proper x (-1)

(* Tests *)

(* TODO: Write a test that calculates (-((double (-1)) + 1)) *)
let test_res1 () =
    let result = None (* implement this *)
    in assert(result = Some 1);
    print_endline "Test for res1 passed!"

(* TODO: Write a test that doubles the value of two and then halves the result. *)
let test_res2 () =
    let result = None (* implement this *)
    in assert(result = Some 2);
    print_endline "Test for res2 passed!"

(* TODO: Write a test that adds two and three together *)
let test_res3 () =
    let result = None (* implement this *)
    in assert(result = Some 5);
    print_endline "Test for res3 passed!"

(* TODO: Write a test that negates the value of three. *)
let test_res4 () =
    let result = None (* implement this *)
    in assert(result = Some (-3));
    print_endline "Test for res4 passed!"

(* TODO: Write a test that divides the value of five by two. *)
let test_res5 () =
    let result = None (* implement this *)
    in assert(result = Some 2);
    print_endline "Test for res5 passed!"

(* TODO: Write a test that negates the sum of four and five. *)
let test_res6 () =
    let result = None (* implement this *)
    in assert(result = Some (-9));
    print_endline "Test for res6 passed!"

(* TODO: Write a test that doubles the sum of one and three. *)
let test_res7 () =
    let result = None (* implement this *)
    in assert(result = Some (-4));
    print_endline "Test for res7 passed!"

(* TODO: Calculate the square of the sum of two and three. *)
let test_res8 () =
    let result = None (* implement this *)
    in assert(result = Some 25);
    print_endline "Test for res8 passed!"

(* TODO: Negate the result of adding four, five, and one together. *)
let test_res9 () =
    let result = None (* implement this *)
    in assert(result = Some (-10));
    print_endline "Test for res9 passed!"

(* TODO: Calculate the sum of doubling three and halving four. *)
let test_res10 () =
    let result = None (* implement this *)
    in assert(result = Some 8);
    print_endline "Test for res10 passed!"

(* Run all tests *)
let run_all_tests () =
    test_res1 ();
    test_res2 ();
    test_res3 ();
    test_res4 ();
    test_res5 ();
    test_res6 ();
    test_res7 ();
    test_res8 ();
    test_res9 ();
    test_res10 ();
    print_endline "All tests passed!"

(* UNCOMMENT THE BELOW LINE TO RUN TESTS *)
(* let _ = run_all_tests () *)
