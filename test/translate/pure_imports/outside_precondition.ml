let wrong () = ()
(*@ wrong () ensures Pure_library.bounded (-1) >= 0 *)
