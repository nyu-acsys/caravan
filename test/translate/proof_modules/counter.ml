module type VIEW = sig
  type t

  (*@ invariant zero (x : t) *)

  val read : t -> int
  (*@ result = read x requires zero x ensures zero x && result = 0 *)
end

module Counter : VIEW = struct
  type t = int Atomic.t

  let read (x : t) = Atomic.get x
end

module Alias = Counter
module Checked : VIEW = Counter

let read_root x = Counter.read x
(*@ result = read_root x
    requires Counter.zero x
    ensures Counter.zero x && result = 0 *)

let read_alias x = Alias.read x
(*@ result = read_alias x
    requires Alias.zero x
    ensures Alias.zero x && result = 0 *)

let read_checked x = Checked.read x
(*@ result = read_checked x
    requires Checked.zero x
    ensures Checked.zero x && result = 0 *)
