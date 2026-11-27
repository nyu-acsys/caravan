
module Integer_key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash key = if key >= 0 then key else -(key + 1)
end
module Integer_set = Make (Integer_key)

module Record_key = struct
  type t = {number : int; flag : bool}
  let equal (left : t) right = left = right
  let hash (_ : t) = 0
end
module Record_set = Make (Record_key)

module Reference_key = struct
  type t = int ref
  let equal (left : t) right = left == right
  let hash (_ : t) = 0
end
module Reference_set = Make (Reference_key)

