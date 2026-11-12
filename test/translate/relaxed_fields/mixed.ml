type cell = {
  mutable first : int; [@caravan.relaxed]
  mutable second : int; [@caravan.relaxed]
  mutable ordinary : int;
}

let allocate first second ordinary = { first; second; ordinary }
(*@ result = allocate first second ordinary
    ensures own result.ordinary ordinary &&
      (exists left : Ghost.t. First.state result first (Set.singleton (left, first))) &&
      (exists right : Ghost.t. Second.state result second (Set.singleton (right, second))) *)

let read_first cell = cell.first
(*@ result = read_first cell
    requires First.state cell current writes && own cell.ordinary other
    ensures First.state cell current writes && own cell.ordinary other &&
      (exists event : Ghost.t. First.observed cell event result && Set.mem (event, result) writes) *)

let client () =
  let cell = allocate 1 2 3 in
  read_first cell
(*@ result = client () ensures result === 1 *)
