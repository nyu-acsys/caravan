module type Reader = sig
  (*@ invariant live (cell : int Atomic.t) *)
  val read : int Atomic.t -> int
  (*@ result = read cell
      opens { live cell }
      requires live cell
      ensures live cell && result = 7 *)
end

module Native = struct
  let read (cell : int Atomic.t) = Atomic.get cell
end

module Make (R : Reader) = struct
  let read cell = R.read cell
  (*@ result = read cell
      opens { R.live cell }
      requires R.live cell
      ensures R.live cell && result = 7 *)
end

module Instance = Make (Native)

let read cell = Instance.read cell
(*@ result = read cell
    opens { Native.live cell }
    requires Native.live cell
    ensures Native.live cell && result = 7 *)
