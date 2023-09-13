
let generate_duck_helper duckNum currentNum =
    if currentNum > 2 then
        string_of_int currentNum ^ " little ducks went swimming one day
        Over the hills and far away
        The mama duck said, 'Quack, quack, quack, quack' And only " ^
        string_of_int (currentNum - 1) ^ " little ducks came back"
    else 
        if currentNum = 2 then 
            string_of_int currentNum ^ " little ducks went swimming one day
            Over the hills and far away
            The mama duck said, 'Quack, quack, quack, quack' And only " ^
            string_of_int (currentNum - 1) ^ " little duck came back"
        else
            if currentNum = 1 then
                string_of_int currentNum ^ " little duck went swimming one day
                Over the hills and far away
                The mama duck said, 'Quack, quack, quack, quack'
                And then no more little ducks came back"
            else
                "Mama duck went swimming one day
                Over the hills and far away
                The mama duck said, 'Quack, quack, quack, quack' And all " ^
                string_of_int (duckNum) ^ " little ducks came back"


(* THIS DOES NOT MAKE HELPER REMEMBER ORIGINAL AMOUNT *)
let generate_duck_verse duckNum =
    generate_duck_helper(duckNum, duckNum) :: generate_duck_verse(duckNum - 1)

let print_duck_verse duckNum
(* simply prints the verse(s))