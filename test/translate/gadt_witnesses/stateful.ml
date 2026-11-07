(* A witness function with effects and a contract that does not mention the witness. *)

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

let take_exn (stack : int list ref) = take stack Value
(*@ r = take_exn stack
    requires own stack.contents xs
    ensures match xs with [] -> own stack.contents [] | _ :: rest -> own stack.contents rest
    raises Not_found -> xs = [] && own stack.contents [] *)
