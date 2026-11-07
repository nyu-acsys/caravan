(* Local functions that use variables of their context, which their contracts name as the
   code does, written with function, and applied with @@. *)

let count_down (n : int) =
  let stop = 0 in
  let rec go k =
    if k <= stop then stop else go (k - 1)
    (*@ r = go k
      requires stop = 0
      ensures r = 0 *)
  in
  go n
(*@ r = count_down n
    ensures r = 0 *)

let first_or (d : int) =
  let pick = function
    | [] -> d
    | x :: _ -> x
    (*@ r = pick xs
      ensures match xs with [] -> r = d | x :: _ -> r = x *)
  in
  pick @@ [ 1; 2 ]
(*@ r = first_or d
    ensures r = 1 *)
