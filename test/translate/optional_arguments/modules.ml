module type Select = sig
  val choose : 'a -> ?value:'a -> unit -> 'a
  (*@ result = choose fallback value token
      ensures result === (match value with None -> fallback | Some v -> v) *)
end

module Native = struct
  let choose fallback ?(value = fallback) () = value
end

module Make (Select : Select) = struct
  let choose fallback ?value () = Select.choose fallback ?value ()
end

module Instance = Make (Native)
module Alias = Instance

let client () =
  assert (Alias.choose 42 () = 42);
  assert (Alias.choose 42 ~value:7 () = 7);
  assert (Alias.choose true ());
  assert (not (Alias.choose true ?value:(Some false) ()))
