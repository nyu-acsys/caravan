let wrong (value : bool) = Pure_library.identity value
(*@ result = wrong value ensures result =/= value *)
