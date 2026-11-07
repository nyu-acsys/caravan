module type Ordinary = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x requires counter x n ensures counter x n && result = n *)
  val touch : t -> unit
  (*@ touch x requires counter x n ensures counter x n *)
end

module type Atomic = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = atomic read x atomic requires counter x n atomic ensures counter x n && result = n *)
  val touch : t -> unit
  (*@ atomic touch x atomic requires counter x n atomic ensures counter x n *)
end

module First : Ordinary
module Second : Ordinary
module Atomic_first : Atomic
module Atomic_second : Atomic

module type Strong_ordinary = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x requires counter x n && n >= 0 ensures counter x n && result = n *)
  val touch : t -> unit
  (*@ touch x requires counter x n && n >= 0 ensures counter x n *)
end

module type Strong_atomic = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = atomic read x atomic requires counter x n && n >= 0 atomic ensures counter x n && result = n *)
  val touch : t -> unit
  (*@ atomic touch x atomic requires counter x n && n >= 0 atomic ensures counter x n *)
end

module Strong_First : Strong_ordinary
module Strong_Atomic_first : Strong_atomic
