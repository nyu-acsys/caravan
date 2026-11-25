module Instance : sig
  type t

  (*@ invariant stored (cell : t) (original [@implicit] : t) *)
  val keep : t -> t
  (*@ result = keep cell requires stored cell original
      ensures stored result original && result === cell *)
end

module Again : sig
  type t = Instance.t

  (*@ invariant stored (cell : t) (original [@implicit] : t) *)
  val keep : t -> t
  (*@ result = keep cell requires stored cell original
      ensures stored result original && result === cell *)
end

module Native : sig
  type t

  (*@ invariant stored (cell : t) *)
  val keep : t -> t

  (*@ result = keep cell requires stored cell
      ensures stored result && result === cell *)
  val fresh : t -> t
  (*@ result = fresh cell requires stored cell
      ensures stored result && result === cell *)
end

module Container : sig
  module Key : sig
    type t = { number : int }
  end

  module Inner : sig
    type t

    (*@ invariant stored (cell : t) (key [@implicit] : Key.t) *)
    val keep : t -> t
    (*@ result = keep cell requires stored cell key
        ensures stored result key && result === cell *)
  end
end

val use : Instance.t -> Again.t
(*@ result = use cell requires Instance.stored cell cell
    ensures Again.stored result cell && result === cell *)
