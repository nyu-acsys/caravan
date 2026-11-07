module Scope = struct
  module type Argument = sig end

  module Make (X : Argument) = struct
    let incorrect (x : int) = x
    (*@ result = incorrect x ensures result = x + 1 *)
  end
end
