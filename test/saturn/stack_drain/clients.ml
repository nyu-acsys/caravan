let integers () =
  let stack = Treiber_stack.create () in
  Treiber_stack.push stack 1;
  Treiber_stack.push stack 2;
  assert (Stack_drain.drain stack = [ 2; 1 ]);
  assert (Treiber_stack.is_empty stack)

let booleans () =
  let stack = Treiber_stack.create () in
  Treiber_stack.push stack true;
  Treiber_stack.push stack false;
  assert (Stack_drain.drain stack = [ false; true ]);
  assert (Treiber_stack.is_empty stack)

let mutable_payload () =
  let value = ref 7 in
  let stack = Treiber_stack.create () in
  Treiber_stack.push stack value;
  begin match Stack_drain.drain stack with
  | [ result ] ->
      assert (result == value);
      result := 11;
      assert (!value = 11)
  | _ -> assert false
  end;
  assert (Treiber_stack.is_empty stack)
