exception Missing

let choose ?(value = raise Missing) () = value
let supplied () = choose ~value:42 ()
let caught () : int = try choose () with Missing -> 7
