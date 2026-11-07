module Lists : sig
  val add : int list -> int -> int list
  (*@ result = add values value
      ensures result = [value] @ values && List.mem value result *)
end = struct
  let add values value = value :: values
end

let singleton value = Lists.add [] value
(*@ result = singleton value ensures result = [value] *)
