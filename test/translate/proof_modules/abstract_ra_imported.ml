module A = struct end

module Make (X : Ra_view.VIEW) = struct
  let mark (value : int) = value
end

module One = Make (A)
