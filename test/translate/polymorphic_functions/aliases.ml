let id value = value

(*@ result = id value pure ensures result === value *)
let alias = id
let chained = alias

module Names = struct
  let identity = chained
  let again = identity
end

module Renamed = Names

let integer (value : int) = Renamed.again value
(*@ result = integer value ensures result === value *)

let boolean (value : bool) = alias value
(*@ result = boolean value ensures result === value *)

let integers (values : int list) = Names.identity values
(*@ result = integers values ensures result === values *)
