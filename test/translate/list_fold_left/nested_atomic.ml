let read (source : int Atomic.t) = Atomic.get source
(*@ result = read source
    requires own source value
    ensures own source value && result = value *)

let copied source = Atomic.make (read source)
(*@ result = copied source
    requires own source value
    ensures own source value && own result value *)
