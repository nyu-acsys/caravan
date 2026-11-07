module Outer : sig
  module Left : sig end
  module Right : sig end
end = struct
  module Left = struct
    type t = int Atomic.t

    let read (cell : t) = Atomic.get cell
    (*@ Ghost.scope (fun step ->
        let token = Read.bind () in
        let value = Read.access token cell in
        unfold contents cell value;
        let result = step () in
        fold contents cell value;
        Read.commit token cell result;
        result)
    *)
    (*@ manual *)
    (*@ result = atomic read cell
        atomic requires contents cell value
        atomic ensures contents cell value && result = value *)
  end

  module Alias = Left

  module Right = struct
    let read (cell : int Atomic.t) = Atomic.get cell
    (*@ Ghost.scope (fun step ->
        let token = Read.bind () in
        let value = Read.access token cell in
        unfold contents cell value;
        let result = step () in
        fold contents cell value;
        Read.commit token cell result;
        result)
    *)
    (*@ manual *)
    (*@ result = atomic read cell
        atomic requires contents cell value
        atomic ensures contents cell value && result = value *)
  end

  module Helper = struct end
end
