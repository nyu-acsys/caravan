let wrong () = ()
(*@ wrong () ensures Pure_library.identity (max_int + 1) <= max_int *)
