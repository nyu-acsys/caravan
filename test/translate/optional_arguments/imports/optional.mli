val choose : 'a -> ?value:'a -> unit -> 'a
(*@ result = choose fallback value token
    ensures result === (match value with None -> fallback | Some v -> v) *)
