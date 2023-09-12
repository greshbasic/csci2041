let foo x y
  = x + y

let plus x y
  = string_of_int x ^ " plus " ^
    string_of_int y ^ " is " ^
    string_of_int (foo x y)

let user_number_x = read_int ()
let user_number_y = read_int ()
let () = print_endline(plus user_number_x user_number_y)