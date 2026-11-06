module type Operation = sig
  val apply : int -> int
  (*@ result = apply x *)
end

module Make (X : Operation) = struct
  let identity x = X.apply x
  (*@ result = identity x ensures result = x *)
end

module Identity = struct
  let apply (x : int) = x
  (*@ result = apply x ensures result = x *)
end

module Instance = Make (Identity)
