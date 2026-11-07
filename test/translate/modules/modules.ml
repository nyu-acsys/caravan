let outer (value : int) = value
(*@ result = outer value ensures result = value *)

module Left = struct
  type t = Value of int
  type record = { value : int }

  let get (item : t) = match item with Value value -> outer value
  (*@ result = get item ensures match item with Value value -> result = value *)

  let field item = item.value
  (*@ result = field item ensures result = item.value *)

  module Inner = struct
    let call value = get (Value value)
    (*@ result = call value ensures result = value *)
  end
end

module Right = struct
  type t = Value of bool
  type record = { value : bool }

  let get (item : t) = match item with Value value -> value
  (*@ result = get item ensures match item with Value value -> result = value *)

  let field item = item.value
  (*@ result = field item ensures result = item.value *)

  let captured (value : bool) count =
    let rec loop remaining =
      if remaining <= 0 then value else loop (remaining - 1)
      (*@ result = loop remaining ensures result = value *)
    in
    loop count
  (*@ result = captured value count ensures result = value *)
end

let nested value = Left.Inner.call value
(*@ result = nested value ensures result = value *)
