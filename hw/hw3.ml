let leftover_count lst x = 
  List.fold_left (
    fun accu h ->
      match h with
      | num -> if accu <= 0 then (num - 1) else (accu - 1)
  ) x lst

let last_card lst x =
  let (_, resetNum) = (List.fold_left (
    fun (accu, resetNum) h ->
      match h with
      | num -> if accu <= 0 then ((num-1),(num)) else ((accu-1),(resetNum))
    ) (x, -1) lst
  ) in resetNum

let num_greater_than_sum lst =
  let (accu,_) = (List.fold_left (
    fun (accu, sum) h ->
      match h with
      | num -> if h > sum then ((accu + 1),(sum + num)) else ((accu),(sum + num)) 
    ) (0, 0) lst
  ) in accu