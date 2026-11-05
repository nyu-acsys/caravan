module Lists = Stdlib.List

let reverse_pair left right = List.rev [ left; right ]
(*@ result = reverse_pair left right
    ensures result === [right; left] *)

let prepend_reversed first second rest = List.rev_append [ first; second ] rest
(*@ result = prepend_reversed first second rest
    ensures result === second :: first :: rest *)

let reverse_empty () : int list = Stdlib.List.rev []
(*@ result = reverse_empty ()
    ensures result === [] *)

let reverse_alias (values : int list) = Lists.rev values
(*@ result = reverse_alias values
    ensures result === Stdlib.List.rev values *)

let append_open values rest =
  let open Stdlib.List in
  rev_append values rest
(*@ result = append_open values rest
    ensures result === List.rev values @ rest *)

let reverse_bools () = List.rev [ true; false ]
(*@ result = reverse_bools ()
    ensures result === [false; true] *)

let reverse_nested () = List.rev [ [ 1 ]; [ 2; 3 ] ]
(*@ result = reverse_nested ()
    ensures result === [[2; 3]; [1]] *)

let locally_opened () = List.(rev [ 1; 2 ])
(*@ result = locally_opened ()
    ensures result === [2; 1] *)

let locally_opened_nested () = List.(rev [ [ 1 ]; [ 2; 3 ] ])
(*@ result = locally_opened_nested ()
    ensures result === [[2; 3]; [1]] *)

let alias_head (values : int Stdlib.List.t) =
  List.(match values with [] -> 0 | value :: _ -> value)
(*@ result = alias_head values
    ensures min_int <= result <= max_int *)

let specification_alias (values : int list) = values
(*@ result = specification_alias values
    ensures (result : int Stdlib.List.t) === values *)

let locally_opened_pure () = List.(rev [ 1; 2 ])
(*@ result = locally_opened_pure ()
    pure
    ensures result === [2; 1] *)

module List = struct
  let rev values = values
  (*@ result = rev values ensures result === values *)
end

let shadowed (values : int list) = List.rev values
(*@ result = shadowed values
    ensures result === values *)

let retained_alias (values : bool list) = Lists.rev values
(*@ result = retained_alias values
    ensures result === Stdlib.List.rev values *)
