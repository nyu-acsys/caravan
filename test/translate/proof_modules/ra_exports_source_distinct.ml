module type VIEW = sig
  type t
  (*@ module R : ResourceAlgebra *)
end

module A : VIEW = struct
  type t = int
end

module B : VIEW = struct
  type t = int
end
