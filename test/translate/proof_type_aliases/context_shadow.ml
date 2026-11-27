module Shadow = struct
  module Ghost = struct
    type t = int ref

    module Mutex = struct
      let context (_owner : t) (_held : Stdlib.Mutex.t list) = false
      (*@ result = context owner held pure ensures result = false *)
    end
  end

  let call owner held = Ghost.Mutex.context owner held
  (*@ result = call owner held
      ensures result = Ghost.Mutex.context owner held && not result *)
end
