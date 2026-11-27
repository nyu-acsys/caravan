module type ELEMENT = sig
  type t
end

module Make (Element : ELEMENT) = struct
  type t = { mutex : Mutex.t }

  let create (value : Element.t) = { mutex = Mutex.create () }

  let work cell =
    Mutex.lock cell.mutex;
    Mutex.unlock cell.mutex
end

module Integer = struct
  type t = int
end

module Instance = Make (Integer)

let client () =
  let cell = Instance.create 7 in
  Instance.work cell
