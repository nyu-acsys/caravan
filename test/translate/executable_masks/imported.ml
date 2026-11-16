let read cell = Reader.read cell
(*@ result = read cell
    opens { Reader.live cell }
    requires Reader.live cell
    ensures Reader.live cell && result = 7 *)
