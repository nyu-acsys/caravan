module type Argument = sig end

module Make (X : Argument) = struct
  type 'a t = Value of 'a
end
