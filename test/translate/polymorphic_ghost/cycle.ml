let make value =
  let cell =
    Atomic.make value
    (*@ initializes [Ghost.init saved None] *)
  in
  (*@ proof fold guarded cell {value = value; remembered = None} *)
  cell
(*@ manual *)
(*@ result = make value ensures guarded result *)

let read (cell : 'a Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Read.bind () in
    let (value, remembered) = unfold guarded cell {value; remembered} in
    Read.access token cell;
    let result = step () in
    fold guarded cell {value = value; remembered = remembered};
    Read.commit token cell result;
    result) *)
(*@ manual *)
(*@ result = atomic read cell
    requires guarded cell
    atomic requires true
    atomic ensures true *)

let both () =
  let integer = make 17 in
  let boolean = make true in
  (read integer, read boolean)
