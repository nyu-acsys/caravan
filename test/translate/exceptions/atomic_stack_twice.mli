val pop_twice : 'a t -> 'a
(*@ r = atomic pop_twice t
    atomic requires stack t xs
    atomic ensures stack t xs
    atomic raises Empty -> stack t xs *)
