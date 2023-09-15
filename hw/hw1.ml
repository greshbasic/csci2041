
let rec generate_duck_helper duckNum currentNum =
    if currentNum > 2 then
        let firstLine = string_of_int currentNum ^ (" little ducks went swimming one day \nOver the hills and far away \nThe mama duck said, " ^ "\"Quack, quack, quack, quack\"" ^ "\nAnd only ") in
        let secondLine = string_of_int (currentNum - 1) ^ (" little ducks came back \n\n") in
        let fullStanza = firstLine ^ secondLine in
        fullStanza :: generate_duck_helper duckNum (currentNum - 1) 
    else if currentNum = 2 then
        let firstLine = string_of_int currentNum ^ (" little ducks went swimming one day \nOver the hills and far away \nThe mama duck said, " ^ "\"Quack, quack, quack, quack\"" ^ "\nAnd only ") in
        let secondLine = string_of_int (currentNum - 1) ^ (" little duck came back \n\n") in
        let fullStanza = firstLine ^ secondLine in
        fullStanza :: generate_duck_helper duckNum (currentNum - 1)
    else if currentNum = 1 then
        let fullStanza = ("1 little duck went swimming one day \nOver the hills and far away \nThe mama duck said, " ^ "\"Quack, quack, quack, quack\"" ^ " \nAnd then no more little ducks came back \n\n") in
        fullStanza :: generate_duck_helper duckNum (currentNum - 1)
    else if currentNum = 0 then
        let firstLine = "Mama duck went swimming one day \nOver the hills and far away \nThe mama duck said, " ^ "\"Quack, quack, quack, quack\"" in
        let secondLine = ("\nAnd all " ^ string_of_int duckNum ^ " little ducks came back") in
        let fullStanza = firstLine ^ secondLine in
        fullStanza :: generate_duck_helper duckNum (currentNum - 1)
    else
        []

let rec sentence_maker sentenceList =
    match sentenceList with
    | [] -> ""
    | h::t -> h ^ sentence_maker t

let generate_duck_verse duckNum =
    let verseList = generate_duck_helper duckNum duckNum in
    let finalizedString = sentence_maker(verseList) in
    finalizedString

let print_duck_verse duckNum = 
    print_endline(generate_duck_verse duckNum)