module Make () = struct
  exception Empty

  let get (x : int) = if x = 0 then raise Empty else x
  (*@ result = get x
      ensures result = x && x <> 0
      raises Empty -> x = 0 *)

  let get_or_zero (x : int) = try get x with Empty -> 0
  (*@ result = get_or_zero x ensures result = x *)
end
