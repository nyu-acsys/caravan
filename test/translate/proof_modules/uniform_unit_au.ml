module World = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)

  module Make () = struct
    let read (value : int) = identity value
    (*@ Ghost.scope (fun step ->
        let token = Read.bind () in
        let result = step () in
        Read.access token value;
        Read.commit token value result;
        result) *)
    (*@ manual *)
    (*@ result = atomic read value
        atomic ensures result = value *)
  end

  module One = Make ()
  module Two = Make ()
  module Alias = One
end

let use_one (value : int) = World.One.read value
(*@ result = use_one value ensures result = value *)

let use_two (value : int) = World.Two.read value
(*@ result = use_two value ensures result = value *)
