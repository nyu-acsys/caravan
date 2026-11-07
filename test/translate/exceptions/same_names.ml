(* Two modules declare exceptions of the same name, which are different exceptions. *)

module Left = struct
  exception Empty

  let check (x : int) = if x = 0 then raise Empty else x
  (*@ r = check x
      ensures r = x && x <> 0
      raises Empty -> x = 0 *)
end

module Right = struct
  exception Empty

  let check (x : int) = if x = 0 then raise Empty else x
  (*@ r = check x
      ensures r = x && x <> 0
      raises Empty -> x = 0 *)
end

(* Right's handler does not catch Left's exception. *)
let left_or (x : int) = try Left.check x with Right.Empty -> 7 | Left.Empty -> 0
(*@ r = left_or x
    ensures r = x *)
