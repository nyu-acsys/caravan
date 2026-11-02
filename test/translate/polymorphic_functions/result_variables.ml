let empty () = []
(*@ result = empty () pure ensures result === [] *)

let lists () = ((empty () : int list), (empty () : bool list))
(*@ result = lists () ensures result === ([], []) *)

let unreachable () = assert false
(*@ result = unreachable () requires false *)

let impossible () = (unreachable () : int)
(*@ result = impossible () requires false *)
