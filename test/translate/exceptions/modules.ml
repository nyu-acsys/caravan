module Stack = struct
  exception Empty

  let top (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
  (*@ r = top xs
      raises Empty -> xs = [] *)
end

let peek xs = Stack.top xs
(*@ r = peek xs
    raises Stack.Empty -> xs = [] *)
