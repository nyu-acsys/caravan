module Model = struct
  module Cell : sig
    type t

    (*@ invariant live (cell : t) *)
    val create : unit -> t
    (*@ cell = create () ensures live cell *)
  end = struct
    type t = int Atomic.t

    let create () = Atomic.make 0
    (*@ initially { value = 0; ready = Ready } *)
  end
end

module Other : sig
  type t

  (*@ invariant live (cell : t) *)
  val create : unit -> t
  (*@ cell = create () ensures live cell *)
end = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0; ready = Model.Ready } *)
end
