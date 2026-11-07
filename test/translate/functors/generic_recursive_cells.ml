module Make () = struct
  type unused = Unused of (int * bool)
  type node = Nil | Next of int * node Atomic.t
  type forest = Forest of int * forest list

  let root (value : forest) = match value with Forest (number, _) -> number
  (*@ result = root value ensures min_int <= result && result <= max_int *)

  let create () = Atomic.make Nil
  (*@ cell = create () ensures own cell Nil *)

  let read (cell : node Atomic.t) = Atomic.get cell
  (*@ result = read cell
      requires own cell value
      ensures own cell value && result === value *)
end

module First = Make ()
module Second = Make ()
module Alias = First

let independent () =
  let first = First.create () in
  let second = Second.create () in
  Atomic.set first (First.Next (7, first));
  begin match Alias.read first with
  | First.Nil -> assert false
  | First.Next (value, next) ->
      assert (value = 7);
      assert (next == first)
  end;
  assert (Atomic.get second == Second.Nil)

let mixed () =
  let first = Atomic.make (First.Nil, Second.Nil, First.Nil) in
  let second = Atomic.make (First.Nil, First.Nil, Second.Nil) in
  begin match Atomic.get first with
  | First.Nil, Second.Nil, First.Nil -> ()
  | _ -> assert false
  end;
  match Atomic.get second with
  | First.Nil, First.Nil, Second.Nil -> ()
  | _ -> assert false

let forest (children : First.forest list) = First.root (First.Forest (7, children))
(*@ result = forest children ensures min_int <= result && result <= max_int *)
