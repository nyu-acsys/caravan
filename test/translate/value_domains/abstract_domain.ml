let preserve (value : Imported_values.t) = value
(*@ result = preserve value ensures result === value *)

let received () = Imported_values.make ()
