module type CELL = sig
  type 'a t

  (*@ invariant related (q : 'a t) (value : 'a) *)
end

module Cell : CELL = struct
  type 'a t = 'a Atomic.t
end
