module Counter = struct
  let read (cell : int Atomic.t) = Atomic.get cell
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let value = Read.access token cell in
      let result = step () in
      Read.commit token cell result;
      result) *)
  (*@ manual *)
  (*@ result = atomic read cell
      atomic requires own cell value
      atomic ensures own cell value && result = value *)
end
