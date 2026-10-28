module Left : sig
  type t = int Atomic.t
  (*@ invariant live (root : t) *)

  val create : unit -> t

  (*@ root = create () ensures live root *)
  val remember : t -> t -> unit
  (*@ remember root x requires live root
      requires past (mem x s.cells)
      ensures live root *)
end = struct
  type t = int Atomic.t

  let create () = Atomic.make 0

  (*@ initially { cells = [] } *)
  let remember root x = ()
end

module Right : sig
  type t = int Atomic.t
  (*@ invariant live (root : t) *)

  val create : unit -> t

  (*@ root = create () ensures live root *)
  val remember : t -> t -> unit
  (*@ remember root x requires live root
      requires past (mem x s.cells)
      ensures live root *)
end = struct
  type t = int Atomic.t

  let create () = Atomic.make 0

  (*@ initially { cells = [] } *)
  let remember root x = ()
end
