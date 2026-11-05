let reverse_twice (values : 'a list) = List.rev (List.rev values)
(*@ result = reverse_twice values ensures result === values *)

let reverse_append (values : 'a list) (suffix : 'a list) =
  List.rev_append (List.rev values) suffix
(*@ result = reverse_append values suffix ensures result === values @ suffix *)
