let choose cell
    ?(value =
      cell := 1;
      42) () =
  value
(*@ result = choose cell value token pure ensures true *)
