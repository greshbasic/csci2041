module type ProperS =
sig
	val plus : int -> int -> int option
	val divide : int -> int -> int option
	val subtract : int -> int -> int option
end

(* Write the functions defined in the above signature 
	Note: these functions are the same as the ones given
	in previous labs and lectures *)
module Proper = struct
	(* let plus ... *)
	let ( >>= ) (opt: 'a option) (f: ('a -> 'b option)) : 'b option =
    match opt with
    | Some x -> f x
    | None -> None

	let plus x y = 
		let s = x + y in  
		match (x >= 0, y >= 0, s >= 0) with  
		| (true, true, true)
		| (false, false, false)
		| (true, false, _)
		| (false, true, _) -> Some s  
		| (_, _, _) -> None

	let divide x y = 
		match x, y with
		| _ when x = min_int && y = (-1) -> None
		| _, 0 -> None
		| _ -> Some (x / y)
	(*
	   Create the negate function:
	   type: int -> int option
	   note: this function returns None if the input equals min_int 
	*)
	(* let negate ... *)
	let negate x = divide x (-1)
	(* use negate then plus in the subtract function *)
	(* let subtract ... *)
	let subtract x y = 
		let negated_y = negate y in
			match negated_y with
			| Some n -> plus x n
			| _ -> None
end


(* When you are finished writing the functions, 
	uncomment the below line. Then remove multiply 
	from the signature and try again *)

module Test = (Proper: ProperS)

(* TESTS *)

(* This line should pass *)
let _  = Test.subtract 3 1

(* This line should fail *)
let _  = Test.negate 1
