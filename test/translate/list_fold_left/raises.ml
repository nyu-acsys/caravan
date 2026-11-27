exception Stop

let stop (values : bool list) =
  List.fold_left (fun () value -> if value then raise Stop else ()) () values
(*@ result = stop values
    ensures result = ()
    raises Stop *)

let handled values = try stop values with Stop -> ()
