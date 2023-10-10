type tree =
  | Leaf
  | Node of int * tree * tree


let with_default default op =
  match op with 
  | None -> default
  | Some n -> n


module Tree_ops =
struct 
  let rec sum t = 
    match t with 
    | Leaf -> 0
    | Node (num, left, right) -> num + sum(left) + sum(right)
  
                                      
  let rec tmax t =
    let max x y = if x >= y then x else y in
    match t with
    | Leaf -> None
    | Node (num, left, right) -> (
      match (tmax left), (tmax right) with
      | (Some x, Some y) -> Some(max (max x y) num)
      | (Some x, None) -> Some(max x num)
      | (None, Some y) -> Some(max y num)
      | _ -> Some(num)
    )
          
  let rec flatten t =
    match t with
    | Leaf -> [] 
    | Node (num, left, right) -> flatten(left) @ [num] @ flatten(right)
       
    
  let rec sortedChecker t_arr = 
    match t_arr with
    | h1::h2::t ->if h1 > h2 then false else sortedChecker (h2::t)
    | _ -> true
    
  
  let is_tree_sorted t =
    sortedChecker (flatten t)


end