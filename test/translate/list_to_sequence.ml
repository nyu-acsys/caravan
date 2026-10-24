let identity (values : int list) = values
(*@ result = identity values ensures to_sequence result = to_sequence values *)
