module Abstract : sig
  type t

  val make : unit -> t
end = struct
  type t = int Atomic.t

  let make () = Atomic.make 0
end

let client (value : Abstract.t) = ()
(*@ client value requires own value 0 *)
