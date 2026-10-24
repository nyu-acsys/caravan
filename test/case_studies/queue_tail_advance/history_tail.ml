let swing_tail q =
  let old_tail = Atomic.get q.tail in
  match Atomic.get old_tail with
  | Nil -> ()
  | Next (_, next) -> if Atomic.compare_and_set q.tail old_tail next then () else ()
(*@ swing_tail q requires is_queue q *)
