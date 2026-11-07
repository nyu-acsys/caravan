let keep value =
  let step () = value in
  (*@ result = step () ensures result === value *)
  step ()
(*@ result = keep value ensures result === value *)

let choose value count =
  let rec loop count = if count = 0 then value else loop (count - 1) in
  (*@ result = loop count
      requires count >= 0
      ensures result === value *)
  loop count
(*@ result = choose value count
    requires count >= 0
    ensures result === value *)

type 'a node = Nil | Next of 'a * 'a node Atomic.t
type 'a t = { head : 'a node Atomic.t Atomic.t; tail : 'a node Atomic.t Atomic.t }

let of_list list =
  let tail_ = Atomic.make Nil in
  let tail = Atomic.make_contended tail_ in
  let rec build_next = function
    | [] -> tail_
    | hd :: tl -> Atomic.make @@ Next (hd, build_next tl)
    (*@ result = build_next xs
        requires own tail_ Nil
        ensures own tail_ Nil *)
  in
  let head = Atomic.make_contended @@ build_next list in
  { head; tail }

let push_cell cell value =
  let next = Atomic.make Nil in
  let node = Next (value, next) in
  let rec find_tail_and_enq curr_end node =
    if not (Atomic.compare_and_set curr_end Nil node) then
      match Atomic.get curr_end with
      | Nil -> find_tail_and_enq curr_end node
      | Next (_, successor) -> find_tail_and_enq successor node
    (*@ find_tail_and_enq curr_end node
        requires own curr_end Nil
        ensures own curr_end node *)
  in
  find_tail_and_enq cell node;
  next
(*@ result = push_cell cell value
    requires own cell Nil
    ensures own cell (Next (value, result)) && own result Nil *)

let clients () =
  assert (keep 17 = 17);
  assert (keep true);
  assert (choose 23 3 = 23);
  assert (choose false 2 = false);
  let (_ : int t) = of_list [ 17; 23 ] in
  let (_ : bool t) = of_list [ true; false ] in
  let cell = Atomic.make Nil in
  let _ = push_cell cell 17 in
  (match Atomic.get cell with
  | Nil -> assert false
  | Next (value, _) -> assert (value = 17));
  let cell = Atomic.make Nil in
  let _ = push_cell cell true in
  (match Atomic.get cell with Nil -> assert false | Next (value, _) -> assert value);
  ()
