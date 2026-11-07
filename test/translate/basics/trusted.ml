(* A trusted function, whose body Caravan does not translate, and a caller relying on its
   contract. *)

let digits (n : int) = String.length (string_of_int n)
(*@ r = digits n
    ensures r >= 1 *)
(*@ trusted *)

let at_least_one (n : int) = digits n
(*@ r = at_least_one n
    ensures r >= 1 *)
