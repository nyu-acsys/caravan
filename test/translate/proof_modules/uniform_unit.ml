module World = struct
  module Make () = struct
    let marker (value : int) = value
    (*@ result = marker value ensures result = value *)
  end

  module One = Make ()
  module Two = Make ()
  module Alias = One
end
