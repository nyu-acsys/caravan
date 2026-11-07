type 'a t = 'a Atomic.t

let make value =
  let cell =
    Atomic.make value
    (*@ initializes [Ghost.init saved value] *)
  in
  cell
(*@ result = make value
    ensures own result value && own (Ghost.at saved result) value *)

let both () = (make 17, make true)
(*@ result = both ()
    ensures let (integer, boolean) = result in
      own integer 17 && own boolean true &&
      own (Ghost.at saved integer) 17 && own (Ghost.at saved boolean) true *)
