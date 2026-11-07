module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
end

module type VIEW_ALIAS = VIEW

module A = struct end
module A_alias = A

module Make (X : VIEW) = struct
  let mark (value : int) = value
end

module Make_alias (X : VIEW_ALIAS) = struct
  let mark (value : int) = value
end

module One = Make (A_alias)
module Two = Make_alias (A_alias)
