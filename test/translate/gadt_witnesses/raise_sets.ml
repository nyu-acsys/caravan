(* Calls with a witness that cannot raise need no raises clause. *)

type ('a, _) poly = Option : ('a, 'a option) poly | Value : ('a, 'a) poly

let take : type a r. a list ref -> (a, r) poly -> r =
 fun stack poly ->
  match !stack with
  | [] -> ( match poly with Option -> None | Value -> raise Not_found)
  | x :: rest ->
      stack := rest;
      begin match poly with Option -> Some x | Value -> x
      end
(*@ r = take stack poly
    requires own stack.contents xs
    ensures match xs with [] -> own stack.contents [] | _ :: rest -> own stack.contents rest
    raises Not_found -> xs = [] && own stack.contents [] *)

let take_opt (stack : int list ref) = take stack Option
(*@ r = take_opt stack
    requires own stack.contents xs
    ensures match xs with [] -> own stack.contents [] | _ :: rest -> own stack.contents rest *)

(* Without a contract: the analysis alone. *)
let rec first : type a r. a list -> (a, r) poly -> r =
 fun xs poly ->
  match xs with
  | [] -> ( match poly with Option -> None | Value -> raise Not_found)
  | x :: _ -> ( match poly with Option -> Some x | Value -> x)

let first_opt (xs : int list) = first xs Option
(*@ r = first_opt xs *)
