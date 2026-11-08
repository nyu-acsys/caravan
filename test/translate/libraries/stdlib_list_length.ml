module Lists = Stdlib.List

let empty () = List.length ([] : int list)
(*@ result = empty () ensures result = 0 *)

let pair first second = List.length [ first; second ]
(*@ result = pair first second ensures result = 2 *)

let aliased values = Lists.length values
(*@ result = aliased values
    requires List.length values <= max_int
    ensures result = List.length values *)

let opened values =
  let open Stdlib.List in
  length values
(*@ result = opened values
    requires List.length values <= max_int
    ensures result = List.length values *)

let pure_length (values : 'a list) = List.length values
(*@ result = pure_length values pure
    requires List.length values <= max_int
    ensures result = List.length values *)

let mathematical (values : 'a list) = values
(*@ result = mathematical values
    ensures List.length result = length (to_sequence values)
      && List.length result >= 0 *)

module List = struct
  let length (_values : 'a list) = 42
  (*@ result = length values pure ensures result = 42 *)
end

let shadowed values = List.length values
(*@ result = shadowed values ensures result = 42 && List.length values = 42 *)
