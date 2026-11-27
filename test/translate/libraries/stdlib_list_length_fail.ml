let unchecked (values : int list) = List.length values
(*@ result = unchecked values ensures result = List.length values *)
