type t = int Atomic.t

let create () = Atomic.make 0
(*@ initially { value = 0 } *)

let rec set_one c = if Atomic.compare_and_set c 0 1 then () else set_one c

(* A successful no-op is not the declared transition from zero to one. *)
let rec wrong_action c = if Atomic.compare_and_set c 0 0 then () else wrong_action c

(* No invariant state can contain two. *)
let forbidden_update c = if Atomic.compare_and_set c 0 2 then () else ()

(* A committed read cannot return two. *)
let wrong_result c = Atomic.get c (*@ commit *)
