module Counter : sig
  type t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)

  val create : unit -> t

  (*@ c = create () ensures is_counter c && counter c 0 *)
  val set_one : t -> unit

  (*@ atomic set_one c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c 1 && n = 0 *)
  val read : t -> int
  (*@ result = atomic read c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c n && result = n *)
end = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0 } *)

  let rec set_one c =
    if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c

  let read c = Atomic.get c (*@ commit *)
end

module Alias = Counter

module Other : sig
  type t = int Atomic.t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)

  val create : unit -> t

  (*@ c = create () ensures is_counter c && counter c 0 *)
  val set_one : t -> unit

  (*@ atomic set_one c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c 2 && n = 0 *)
  val read : t -> int
  (*@ result = atomic read c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c n && result = n *)
end = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0 } *)

  let rec set_one c = if Atomic.compare_and_set c 0 2 then () else set_one c
  let read c = Atomic.get c (*@ commit *)
end

module Other_alias = Other

let client () =
  let first = Alias.create () in
  let second = Other_alias.create () in
  Alias.set_one first;
  Other_alias.set_one second;
  Alias.read first + Other_alias.read second
(*@ result = client () ensures result = 3 *)
