let reset (cell : int Atomic.t) (values : int list) =
  List.fold_left
    (fun (current, marker) _value ->
      Atomic.set current 0;
      (current, marker))
    (cell, ()) values
(*@ result = reset cell values
    requires own cell 0
    ensures result === (cell, ()) && own cell 0 *)

let allocate (values : int list) =
  let initial = Atomic.make 0 in
  List.fold_left (fun _previous value -> Atomic.make value) initial values
(*@ result = allocate values
    ensures exists value : int. own result value *)

let saved (cell : int Atomic.t) (values : int list) =
  let _ = Atomic.get cell in
  List.fold_left
    (fun current _value ->
      let _ = Atomic.get current in
      current)
    cell values
(*@ result = saved cell values
    requires own cell value
    ensures result === cell && own cell value *)
