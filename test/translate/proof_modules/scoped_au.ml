module Counter = struct
  type t = int Atomic.t

  let read (cell : t) = Atomic.get cell
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let again = Read.bind () in
      assert (token === again);
      let value = Read.access again cell in
      unfold contents cell value;
      let result = step () in
      fold contents cell value;
      Read.commit token cell result;
      result) *)
  (*@ manual *)
  (*@ result = atomic read cell
      atomic requires contents cell value
      atomic ensures contents cell value && result = value *)
end

module Alias = Counter

let client cell = Alias.read cell
(*@ result = client cell
    requires Alias.contents cell value
    ensures Alias.contents cell value && result = value *)
