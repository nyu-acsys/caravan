val read : 'a Atomic.t -> 'a
(*@ result = read [@atomic] cell
    requires own cell value
    ensures own cell value && result === value *)
