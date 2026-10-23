type node = End | Next of int ref

let same (a : int ref) (b : int ref) = a == b
(*@ result = same a b ensures result = (a == b) *)

let is_end (node : node) = node = End
(*@ result = is_end node ensures result = (node = End) *)

let is_empty (nodes : int ref list) = nodes = []
(*@ result = is_empty nodes ensures result = (nodes = []) *)

let scalar (a : int) (b : int) = a = b
(*@ result = scalar a b ensures result = (a = b) *)
