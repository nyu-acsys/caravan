module Backoff = struct
  type t = unit

  let default = ()
  let once () = ()
end

let wrap3 n =
  let n = n land 7 in
  if n >= 4 then n - 8 else n

let ( + ) left right = wrap3 Stdlib.(left + right)
let ( - ) left right = wrap3 Stdlib.(left - right)
let pause_armed = Atomic.make false
let target_paused = Atomic.make false
let release_target = Atomic.make false

let after_capacity () =
  if Atomic.compare_and_set pause_armed true false then begin
    Atomic.set target_paused true;
    while not (Atomic.get release_target) do
      Domain.cpu_relax ()
    done
  end
