type fields = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : bool; [@caravan.relaxed]
}

let read (cell : int Atomic.t) = Atomic.get cell
(*@ result = read cell
    requires own ~fraction:Permission.half cell value
    ensures own ~fraction:Permission.half cell value && result = value *)
