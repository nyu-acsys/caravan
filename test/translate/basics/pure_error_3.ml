let rec f (n : int) = if n <= 0 then 0 else f (n - 1)
(*@ r = f n
    variant n *)
