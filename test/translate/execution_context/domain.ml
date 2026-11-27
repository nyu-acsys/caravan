type fields = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : bool; [@caravan.relaxed]
}

let work () = 0
(*@ result = work () ensures result === 0 *)

let launch () =
  let child = Domain.spawn work in
  Domain.join child
(*@ result = launch () ensures result === 0 *)
