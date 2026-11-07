module type Element = sig
  type t
end

module Worker (A : Element) = struct
  let work (value : A.t) = value
  (*@ result = work value ensures result === value *)

  let launch value = Domain.spawn (fun () -> work value)
  (*@ domain = launch value ensures Job.handle domain value *)

  let finish (domain : A.t Domain.t) (value : A.t) = Domain.join domain
  (*@ result = finish domain value
      requires Job.handle domain value
      ensures result === value *)

  let client value =
    let domain = launch value in
    finish domain value
  (*@ result = client value ensures result === value *)

  let echo value = value
  (*@ result = echo value ensures result === value *)

  let polymorphic value =
    let domain = Domain.spawn (fun () -> echo value) in
    Domain.join domain
  (*@ result = polymorphic value ensures result === value *)

  let echo_launch value = Domain.spawn (fun () -> echo value)
  (*@ domain = echo_launch value ensures Echo.handle domain value *)

  let concrete (value : A.t) =
    let domain = Domain.spawn (fun () -> echo value) in
    Domain.join domain
  (*@ result = concrete value ensures result === value *)
end

module Int = struct
  type t = int
end

module Bool = struct
  type t = bool
end

module First = Worker (Int)
module Again = Worker (Int)
module Second = Worker (Bool)

module Other = struct
  type t = int
end

module Third = Worker (Other)
module Alias = First

let client () =
  let first = Alias.launch 7 in
  let second = Second.launch true in
  let flag = Second.finish second true in
  let number = Again.finish first 7 in
  assert flag;
  number
(*@ result = client () ensures result === 7 *)

let direct () =
  let domain = Domain.spawn (fun () -> First.work 7) in
  Domain.join domain
(*@ result = direct () ensures result === 7 *)

let returned () =
  let domain = First.launch 7 in
  Domain.join domain
(*@ result = returned () ensures result === 7 *)

let polymorphic_client () =
  let direct = Domain.spawn (fun () -> First.echo true) in
  let returned = First.echo_launch 7 in
  let number = Domain.join returned in
  let flag = Domain.join direct in
  assert flag;
  number
(*@ result = polymorphic_client () ensures result === 7 *)
