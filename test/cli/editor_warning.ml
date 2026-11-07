let trusted (n : int) = String.length (string_of_int n)
(*@ result = trusted n ensures result >= 0 *)
(*@ trusted *)
