module World = struct
  module Inner : sig
    val use : int -> int
    (*@ result = use value ensures result = value *)
  end = struct
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
    module Alias = One

    let use (value : int) = One.read value
  end

  let use (value : int) = Inner.use value
  (*@ result = use value ensures result = value *)
end

let client (value : int) = World.use value
(*@ result = client value ensures result = value *)
