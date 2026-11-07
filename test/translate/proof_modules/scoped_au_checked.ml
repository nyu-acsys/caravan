module Counter = struct
  type t = int Atomic.t

  let read (cell : t) = Atomic.get cell
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let value = Read.access token cell in
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

module Checked : sig
  type t = Counter.t

  (*@ predicate contents (cell : t) (value : int) *)
  val read : t -> int
  (*@ result = atomic read cell atomic requires contents cell value
      atomic ensures contents cell value && result = value *)
end =
  Counter
