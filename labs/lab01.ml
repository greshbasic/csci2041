
let multiply x y
  = string_of_int x ^ " multiplied by " ^
    string_of_int y ^ " is " ^
    string_of_int (x * y)


let multStringTable n =
  let rec loop i =
    if i > n then []
    else (multiply n i) :: loop (i+1)
  in loop 1


let user_number = read_int ()
let mult_table = multStringTable(user_number)