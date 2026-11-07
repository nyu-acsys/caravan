module Make () = struct
  type a_b = { mutable c : int }
  type a = { mutable b_c : int }

  let first value = { c = value }
  (*@ result = first value ensures own result.c value *)

  let second value = { b_c = value }
  (*@ result = second value ensures own result.b_c value *)

  let distinct value =
    let x = first value in
    let y = second value in
    x.c <- 0;
    y.b_c
  (*@ result = distinct value ensures result = value *)
end

module First = Make ()
module Second = Make ()

let client value = First.distinct value + Second.distinct 0
(*@ result = client value ensures result = value *)
