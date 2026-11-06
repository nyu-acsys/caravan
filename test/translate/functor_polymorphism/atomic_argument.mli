val read : 'a Atomic.t -> 'a
(*@ result = atomic read cell
    atomic requires own cell value
    atomic ensures own cell value && result === value *)
