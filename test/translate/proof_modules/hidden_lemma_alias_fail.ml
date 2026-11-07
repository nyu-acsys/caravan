module type VIEW = sig
  type t
end

module Secret : VIEW = struct
  type t = int
end

module Alias = Secret
