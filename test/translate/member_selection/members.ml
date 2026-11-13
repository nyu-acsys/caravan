let good value = value
(*@ result = good value ensures result === value *)

let bad () = assert false

module Work = struct
  let good () = 1
  (*@ result = good token ensures result === 1 *)

  let bad () = assert false
end

let outer () =
  let helper () = assert false in
  helper ()

let other () =
  let helper () = () in
  helper ()

let loop n =
  let counter = ref 0 in
  while !counter < n do
    (*@ invariant own counter.contents value && value <= 0 *)
    incr counter
  done
(*@ loop n requires 0 <= n <= 1000 *)

let proved () = 1
