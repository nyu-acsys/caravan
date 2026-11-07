val read : int ref -> int
(*@ result = read cell pure
    requires own cell.contents value
    ensures result === value *)
