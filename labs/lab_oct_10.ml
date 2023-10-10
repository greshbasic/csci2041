module type ProperS =
sig
	val plus : int -> int -> int option
	val divide : int -> int -> int option
	val subtract : int -> int -> int option
	val multiply : int -> int -> int option
end

(* Write the functions defined in the above signature 
	Note: these functions are the same as the ones given
	in previous labs and lectures *)
module Proper = struct
	(* let plus ... *)

	(* let divide ... *)

	(*
	   Create the negate function:
	   type: int -> int option
	   note: this function returns None if the input equals min_int 
	*)
	(* let negate ... *)

	(* use negate then plus in the subtract function *)
	(* let subtract ... *)
end


(* When you are finished writing the functions, 
	uncomment the below line. Then remove multiply 
	from the signature and try again *)

(* module Test = (Proper: ProperS) *)

(* TESTS *)

(* This line should pass *)
(* let _  = Test.subtract 3 1 *)

(* This line should fail *)
(* let _  = Test.negate 1 *)
