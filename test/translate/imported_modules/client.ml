module Ordinary = Nested_cells.Ordinary
module Deep = Nested_cells.Nested
module Atomic = Deep.Atomic

let ordinary cell = Nested_cells.Ordinary.read cell
(*@ result = ordinary cell
    requires Ordinary.holds cell value
    ensures Ordinary.holds cell value && result = value *)

let interface_alias cell =
  let first = Nested_cells.Alias.read cell in
  let second = Ordinary.read cell in
  assert (first = second);
  second
(*@ result = interface_alias cell
    requires Ordinary.holds cell value
    ensures Nested_cells.Alias.holds cell value && result = value *)

let nested_interface_alias cell =
  let first = Deep.Alias.read cell in
  let second = Nested_cells.Nested.Other.read cell in
  assert (first = second);
  second
(*@ result = nested_interface_alias cell
    requires Nested_cells.Nested.Other.holds cell value
    ensures Nested_cells.Nested.Alias.holds cell value && result = value *)

let independent left right =
  let first = Ordinary.read left in
  let second = Deep.Other.read right in
  (first, second)
(*@ result = independent left right
    requires Nested_cells.Ordinary.holds left x && Nested_cells.Nested.Other.holds right y
    ensures Ordinary.holds left x && Deep.Other.holds right y && result = (x, y) *)

let read_alias cell = Atomic.read cell
(*@ result = read_alias cell
    requires Nested_cells.Nested.Atomic.shared cell
          && Nested_cells.Nested.Atomic.ticket cell count
          && Nested_cells.Nested.Atomic.holds cell value
    ensures Atomic.shared cell && Atomic.ticket cell count
          && Atomic.holds cell value && result = value *)

let replace_alias cell replacement =
  let previous = Nested_cells.Nested.Atomic.read cell in
  Atomic.replace cell replacement;
  previous
(*@ result = replace_alias cell replacement
    requires Atomic.shared cell && Atomic.ticket cell count && Atomic.holds cell previous
    ensures Nested_cells.Nested.Atomic.shared cell
          && Nested_cells.Nested.Atomic.ticket cell count
          && Nested_cells.Nested.Atomic.holds cell replacement && result = previous *)

let fresh value =
  let cell = Nested_cells.Nested.Atomic.make value in
  Atomic.read cell
(*@ result = fresh value ensures result = value *)

let other cell = Deep.Other_atomic.read cell
(*@ result = other cell
    requires Nested_cells.Nested.Other_atomic.shared cell
          && Nested_cells.Nested.Other_atomic.ticket cell count
          && Nested_cells.Nested.Other_atomic.holds cell value
    ensures Deep.Other_atomic.shared cell && Deep.Other_atomic.ticket cell count
          && Deep.Other_atomic.holds cell value && result = value *)
