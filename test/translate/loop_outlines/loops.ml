let increment cell = incr cell
let read (cell : int ref) = !cell

let count cell =
  for i = 0 to 9 do
    increment cell
  done;
  !cell

let descending cell =
  for i = 9 downto 0 do
    increment cell
  done;
  !cell

let until_ten cell =
  while !cell < 10 do
    increment cell
  done;
  !cell

let exported cell =
  let start = read cell in
  for i = 0 to 9 do
    increment cell
  done;
  !cell + start

module type Element = sig
  type t
end

module Repeat (A : Element) = struct
  let count cell =
    for i = 0 to 9 do
      increment cell
    done;
    !cell
end

module Int = struct
  type t = int
end

module Worker = Repeat (Int)

let generic cell = Worker.count cell
