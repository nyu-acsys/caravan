module Left = struct
  type t = { mutable count : int }

  let read_raw (x : t) = x.count
  (*@ result = read_raw x
      requires own x.count n
      ensures own x.count n && result = n *)

  let read x = read_raw x
  (*@ Ghost.scope (fun read ->
      unfold owned x;
      let result = read () in
      fold owned x result;
      result) *)
  (*@ manual *)
  (*@ result = read x requires owned x n ensures owned x n && result = n *)
end

module Right = struct
  type t = { mutable count : int }

  let read_raw (x : t) = x.count
  (*@ result = read_raw x
      requires own x.count n
      ensures own x.count n && result = n *)

  let read x = read_raw x
  (*@ Ghost.scope (fun read ->
      unfold owned x;
      let result = read () in
      fold owned x result;
      result) *)
  (*@ manual *)
  (*@ result = read x requires owned x n ensures owned x n && result = n *)
end

let read_left x = Left.read x
(*@ result = read_left x requires Left.owned x n
    ensures Left.owned x n && result = n *)

let read_right x = Right.read x
(*@ result = read_right x requires Right.owned x n
    ensures Right.owned x n && result = n *)
