let select () = 11
(*@ result = select () ensures result = 11 *)

let saved () = select ()
(*@ result = saved () ensures result = 11 *)

let select () = 22
(*@ result = select () ensures result = 22 *)

let latest () = select ()
(*@ result = latest () ensures result = 22 *)

let use_saved () = saved ()
(*@ result = use_saved () ensures result = saved () && result = 11 *)
