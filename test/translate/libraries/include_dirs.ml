(* Libraries from another directory, given with -I: Ticker, and Backoff, whose interface
   next to this file comes first. *)

let rec spin (n : int) backoff ticker =
  if n > 0 then spin (n - 1) (Backoff.once backoff) (Ticker.tick ticker)

let run () = spin 3 Backoff.default Ticker.start
