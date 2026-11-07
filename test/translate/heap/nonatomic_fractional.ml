type counter = { mutable count : int }

let read_ref (cell : int ref) = !cell
(*@ result = read_ref cell
    requires own ~fraction:Permission.half cell.contents value
    ensures own ~fraction:Permission.half cell.contents value && result = value *)

let read_record (cell : counter) = cell.count
(*@ result = read_record cell
    requires own ~fraction:Permission.half cell.count value
    ensures own ~fraction:Permission.half cell.count value && result = value *)

let destructure (cell : counter) =
  let { count } = cell in
  count
(*@ result = destructure cell
    requires own ~fraction:Permission.half cell.count value
    ensures own ~fraction:Permission.half cell.count value && result = value *)

let read_param { count } = count
(*@ result = read_param cell
    requires own ~fraction:Permission.half cell.count value
    ensures own ~fraction:Permission.half cell.count value && result = value *)

let match_record (cell : counter) = match cell with { count } -> count
(*@ result = match_record cell
    requires own ~fraction:Permission.half cell.count value
    ensures own ~fraction:Permission.half cell.count value && result = value *)

let option_read (cell : counter option) =
  match cell with None -> 0 | Some { count } -> count
(*@ result = option_read cell
    requires match cell with
             | None -> true
             | Some c -> own ~fraction:Permission.half c.count 0
    ensures match cell with
            | None -> result = 0
            | Some c -> own ~fraction:Permission.half c.count 0 && result = 0 *)

let write_ref (cell : int ref) value = cell := value
(*@ write_ref cell value
    requires own cell.contents previous
    ensures own cell.contents value *)

let write_record (cell : counter) value = cell.count <- value
(*@ write_record cell value
    requires own cell.count previous
    ensures own cell.count value *)
