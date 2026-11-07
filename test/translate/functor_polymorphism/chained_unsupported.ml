module type S = sig
  val id : 'a -> 'a
  (*@ result = id value ensures result === value *)
end

module Apply (X : S) = struct
  let id value = X.id value
  (*@ result = id value ensures result === value *)
end

module Native = struct
  let id value = value
  (*@ result = id value ensures result === value *)
end

module A : S = Native
module B : S = A
module Client = Apply (B)

let client () =
  assert (Client.id 17 = 17);
  assert (Client.id true)
