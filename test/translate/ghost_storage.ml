type counter = { mutable value : int }

let make () =
  let cell =
    Atomic.make 0
    (*@ initializes [
    Ghost.init contents [];
    Ghost.init facts (Authority.full (Facts.set Set.empty))
  ] *)
  in
  (*@ lemma publish cell *)
  cell
(*@ result = make ()
    ensures own result 0
    ensures own (Ghost.at contents result) []
    ensures own (Ghost.at facts result) (Authority.full (Facts.set (Set.singleton 0))) *)

let make_ref () =
  let cell =
    (ref 3 : int ref)
    (*@ initializes [Ghost.init reference_tag true] *)
  in
  cell
(*@ result = make_ref ()
    ensures own result.contents 3
    ensures own (Ghost.at reference_tag result) true *)

let make_record () =
  let cell =
    { value = 7 }
    (*@ initializes [Ghost.init record_tag false] *)
  in
  cell
(*@ result = make_record ()
    ensures own result.value 7
    ensures own (Ghost.at record_tag result) false *)

let make_nested () =
  let cell =
    ref @@ ref 0
    (*@ initializes [Ghost.init nested_tag true] *)
  in
  cell
(*@ result = make_nested ()
    ensures own (Ghost.at nested_tag result) true *)

let make_two () =
  let cell =
    Atomic.make (ref 0 (*@ initializes [Ghost.init reference_tag true] *))
    (*@ initializes [Ghost.init outer_tag false] *)
  in
  cell
(*@ result = make_two ()
    ensures own (Ghost.at outer_tag result) false *)

let make_piped () =
  let cell =
    ref 0 |> ref
    (*@ initializes [Ghost.init nested_tag true] *)
  in
  cell
(*@ result = make_piped ()
    ensures own (Ghost.at nested_tag result) true *)

let make_piped_inner () =
  let cell = ref 0 (*@ initializes [Ghost.init reference_tag true] *) |> ref in
  cell
(*@ result = make_piped_inner ()
    ensures exists inner : int ref.
      own result.contents inner && own (Ghost.at reference_tag inner) true *)
