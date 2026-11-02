let ( +. ) value _other = value
(*@ result = (+.) value other pure ensures result === value *)

let integer (value : int) = value +. true
(*@ result = integer value ensures result === value *)

let boolean (value : bool) = value +. 17
(*@ result = boolean value ensures result === value *)

let logical () = ()
(*@ logical ()
    ensures 17 +. false === 17
    ensures true +. 0 === true *)
