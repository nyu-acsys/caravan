module Alias = Pure_library

let integer (value : int) = Alias.identity value
(*@ result = integer value ensures result === Pure_library.identity value *)

let boolean (value : bool) = Pure_library.identity value
(*@ result = boolean value ensures result === value *)

let bounded (value : int) = Pure_library.bounded value
(*@ result = bounded value
    requires value >= 0
    ensures result === Pure_library.bounded value *)

let pure_client (value : int) = Pure_library.identity value
(*@ result = pure_client value
    pure
    ensures result === value *)

let twice value = Pure_library.twice value
(*@ result = twice value ensures result === value *)
