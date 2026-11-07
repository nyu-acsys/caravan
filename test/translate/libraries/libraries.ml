(* A library's functions and values, trusted, as Backoff's. *)

let rec spin (n : int) backoff = if n > 0 then spin (n - 1) (Backoff.once backoff)
let run () = spin 3 Backoff.default
