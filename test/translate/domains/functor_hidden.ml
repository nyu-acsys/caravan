module Worker () : sig
  val run : unit -> int
  (*@ result = run () ensures result === 1 *)
end = struct
  let work () = 1
  (*@ result = work () ensures result === 1 *)

  let run () =
    let domain = Domain.spawn work in
    Domain.join domain
end

module First = Worker ()

let client () = First.run ()
(*@ result = client () ensures result === 1 *)
