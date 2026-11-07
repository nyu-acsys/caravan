module Reader = struct
  let read (cell : int Atomic.t) = Atomic.get cell
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let reg = Ghost.alloc [Ghost.init token_slot token] in
      fold registration reg cell {token = token};
      let result = step () in
      help reg cell result;
      let completed_token = unfold completed reg cell result {token} in
      assert (completed_token = token);
      result)
  *)
  (*@ manual *)
  (*@ result = atomic read cell
      requires own cell 0
      atomic requires zero value
      atomic ensures zero value && result = value *)
end
