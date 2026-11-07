let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
      unfold zero cell;
      let result = step () in
      fold zero cell;
      result) *)
(*@ manual *)
