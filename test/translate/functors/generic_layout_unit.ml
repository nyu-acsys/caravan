module Make () = struct
  type t = Box of int

  let create value = Box value

  (*@ result = create value ensures result = Box value *)
  let get box = match box with Box value -> value
  (*@ result = get box ensures box = Box result *)
end

module First = Make ()
module Second = Make ()

let client value = First.get (First.create value)
(*@ result = client value ensures result = value *)
