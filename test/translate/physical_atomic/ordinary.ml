let read (cell : int ref) = !cell
(*@ result = read [@atomic] cell
    requires own cell.contents value
    ensures own cell.contents value && result = value *)
