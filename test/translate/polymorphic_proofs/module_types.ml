module Static = struct
  let check () = ()
  (*@ check () ensures true *)
end

module Make () = struct
  let keep (value : int) = value
  (*@ result = keep value ensures result === value *)
end

module First = Make ()
module Second = Make ()
module Alias = First

let clients () =
  Static.check ();
  assert (Alias.keep 17 = 17);
  assert (Second.keep 23 = 23)
