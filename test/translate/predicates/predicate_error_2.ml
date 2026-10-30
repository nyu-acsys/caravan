type counter = { mutable count : int }

(*@ predicate valid (c : counter) (n : nat) = own c.count n *)
