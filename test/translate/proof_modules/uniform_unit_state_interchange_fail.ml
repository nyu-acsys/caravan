module type OUTPUT = sig
  type t = int Atomic.t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)

  val create : unit -> t
  (*@ c = create () ensures is_counter c && counter c 0 *)

  val set_one : t -> unit
  (*@ atomic set_one c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c 1 && n = 0 *)
end

module World = struct
  module Make () : OUTPUT = struct
    type t = int Atomic.t

    let create () = Atomic.make 0
    (*@ initially { value = 0 } *)

    let rec set_one c =
      if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c
  end

  module One = Make ()
  module Two = Make ()
end

let wrong () =
  let cell = World.One.create () in
  World.Two.set_one cell
