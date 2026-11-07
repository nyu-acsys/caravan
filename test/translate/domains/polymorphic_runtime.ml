let work value = value
(*@ result = work value ensures result === value *)

let launch value = Domain.spawn (fun () -> work value)
(*@ domain = launch value ensures Job.handle domain value *)

let finish (domain : 'a Domain.t) (value : 'a) = Domain.join domain
(*@ result = finish domain value
    requires Job.handle domain value
    ensures result === value *)

let client () =
  let first = launch 7 in
  let second = launch true in
  let flag = finish second true in
  let number = finish first 7 in
  assert flag;
  number + 1
(*@ result = client () ensures result === 8 *)

let ignore_value value = 3
(*@ result = ignore_value value ensures result === 3 *)

let captured value =
  let domain = Domain.spawn (fun () -> ignore_value value) in
  Domain.join domain
(*@ result = captured value ensures result === 3 *)

let capture_launch value = Domain.spawn (fun () -> ignore_value value)
(*@ domain = capture_launch value ensures Capture.handle domain value *)

let capture_finish (domain : int Domain.t) value = Domain.join domain
(*@ result = capture_finish domain value
    requires Capture.handle domain value
    ensures result === 3 *)

let returned value =
  let domain = capture_launch value in
  let alias = domain in
  Domain.join alias
(*@ result = returned value ensures result === 3 *)

let choose : type a b. a -> b -> b = fun first second -> second
(*@ result = choose first second ensures result === second *)

let reordered first second =
  let domain = Domain.spawn (fun () -> choose first second) in
  Domain.join domain
(*@ result = reordered first second ensures result === second *)

let unit_work () = []
(*@ result = unit_work () ensures result === [] *)

let empty () =
  let domain = Domain.spawn unit_work in
  Domain.join domain
(*@ result = empty () ensures result === [] *)

module type Element = sig
  type t
end

module User (A : Element) = struct
  let run (value : A.t) =
    let domain = Domain.spawn (fun () -> work value) in
    Domain.join domain
  (*@ result = run value ensures result === value *)
end

let monomorphic () = 4
(*@ result = monomorphic () ensures result === 4 *)

let mixed value =
  let first = Domain.spawn monomorphic in
  let second = Domain.spawn (fun () -> work value) in
  let result = Domain.join second in
  let ignored = Domain.join first in
  result
(*@ result = mixed value ensures result === value *)

let transfer (cell : 'a ref) (previous : 'a) (next : 'a) =
  cell := next;
  previous
(*@ result = transfer cell previous next
    requires own cell.contents previous
    ensures own cell.contents next && result === previous *)

let ownership value =
  let cell = ref value in
  let domain = Domain.spawn (fun () -> transfer cell value value) in
  let previous = Domain.join domain in
  !cell
(*@ result = ownership value ensures result === value *)

module Worker = struct
  let echo value = value
  (*@ result = echo value ensures result === value *)
end

module Alias = Worker

let pass (domain : 'a Domain.t) (value : 'a) = domain
(*@ result = pass domain value
    requires Alias.Job.handle domain value
    ensures Worker.Job.handle result value *)

let scoped value =
  let domain = Domain.spawn (fun () -> Alias.echo value) in
  let alias = pass domain value in
  Domain.join alias
(*@ result = scoped value ensures result === value *)

let pick : type a. a -> a -> bool -> a =
 fun left right first -> if first then left else right
(*@ result = pick left right first
    ensures result === (if first then left else right) *)

let local_launch : type a. a -> a Domain.t =
 fun value -> Domain.spawn (fun () -> pick value value true)
(*@ domain = local_launch value ensures Pick.handle domain value value true *)

let local_client value =
  let domain = local_launch value in
  Domain.join domain
(*@ result = local_client value ensures result === value *)
