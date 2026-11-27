type 'a cell = { mutable value : 'a [@caravan.relaxed] [@caravan.raw] }

let make_node value = { value }
let forward value = value
let choose flag first second = if flag then first else second
let select flag first second = match flag with true -> first | false -> second

let nested flag first second =
  let value = if flag then first else second in
  forward value

let load cell = cell.value

let create_dummy () : bool cell =
  let value = Obj.magic () in
  make_node value

let initialize value = make_node value
let transport (cell : 'a cell) = make_node (load cell)
let unit_forward (value : unit) = value

let unit_client () =
  let _ = unit_forward (Obj.magic ()) in
  ()

let unit_prefix () value = value

let aliases () : bool cell * int cell =
  let cleared = Obj.magic () in
  let alias = cleared in
  (make_node alias, make_node cleared)

let choose_dummy flag : bool = choose flag (Obj.magic ()) true
let optional_unit flag value = if flag then value
let direct_alias = forward
let alias_dummy () : bool = direct_alias (Obj.magic ())
let prefix_dummy () : bool = unit_prefix () (Obj.magic ())
let with_ghost value = value
let scoped_forward value = with_ghost value

let wrapped () : bool cell =
  make_node
    (let value = Obj.magic () in
     value)

let sequenced () : bool cell =
  make_node
    (();
     Obj.magic ())

let opened () : bool cell =
  make_node
    (let open Stdlib in
     Obj.magic ())
