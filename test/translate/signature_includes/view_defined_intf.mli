module type Cell = sig
  type 'a t

  (*@ predicate cell (q : 'a t) (value : 'a list) = false *)
end
