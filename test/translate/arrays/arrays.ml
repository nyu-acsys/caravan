let create () =
  let a = Array.make 3 0 in
  a.(1) <- 5;
  a.(1) + Array.length a

let swap (a : int array) i j =
  let x = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- x

let clear (a : int array) =
  for i = 0 to Array.length a - 1 do
    (*@ invariant 0 <= i && i <= Array.length a
        && (forall j : int. 0 <= j && j < i -> own (Array.cell a j) 0)
        && (forall j : int. i <= j && j < Array.length a ->
              exists v : int. own (Array.cell a j) v) *)
    a.(i) <- 0
  done

let first (a : 'a array) = a.(0)
