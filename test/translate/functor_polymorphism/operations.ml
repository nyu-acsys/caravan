module type OPERATIONS = sig
  val id : 'a -> 'a
  (*@ result = id value ensures result === value *)

  val swap : 'a -> 'b -> 'b * 'a
  (*@ result = swap left right ensures result === (right, left) *)
end

module Native = struct
  let id value = value
  (*@ result = id value ensures result === value *)

  let swap first second = (second, first)
  (*@ result = swap first second ensures result === (second, first) *)
end

module Apply (Argument : OPERATIONS) = struct
  let id value = Argument.id value
  (*@ result = id value ensures result === value *)

  let swap left right = Argument.swap left right
  (*@ result = swap left right ensures result === (right, left) *)
end

module Imported = Apply (Argument)
module Direct = Apply (Native)
module Repeated = Apply (Native)
module Alias = Direct

let clients () =
  assert (Imported.id 17 = 17);
  assert (Direct.id true);
  assert (Repeated.id false = false);
  let value = ref 7 in
  assert (Imported.id value == value);
  let result = Alias.id value in
  assert (result == value);
  result := 11;
  assert (!value = 11);
  begin match Imported.swap 23 true with flag, number -> assert (flag && number = 23)
  end;
  begin match Direct.swap false value with
  | cell, flag ->
      assert (cell == value);
      assert (not flag)
  end
