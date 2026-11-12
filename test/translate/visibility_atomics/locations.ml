type unused = { mutable data : int [@caravan.frozen] }
type holder = { cell : int Atomic.t }

let read_record holder = Atomic.get holder.cell
(*@ result = read_record holder
    requires own ~fraction:Permission.half holder.cell value
    ensures own ~fraction:Permission.half holder.cell value && result = value *)

let choose flag (left : int Atomic.t) right = if flag then left else right
(*@ cell = choose flag left right
    ensures cell === (if flag then left else right) *)

let read_expression flag left right = Atomic.get (choose flag left right)
(*@ result = read_expression flag left right
    requires own ~fraction:Permission.half (if flag then left else right) 7
    ensures own ~fraction:Permission.half (if flag then left else right) 7 && result = 7 *)
