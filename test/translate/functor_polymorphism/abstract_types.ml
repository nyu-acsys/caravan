module type CONTAINER = sig
  type 'a t

  val keep : 'a t -> 'a t
  (*@ result = keep value ensures result === value *)
end

module Options = struct
  type 'a t = 'a option

  let keep (value : 'a t) = value
  (*@ result = keep value ensures result === value *)
end

module Keep (Container : CONTAINER) = struct
  let keep value = Container.keep value
  (*@ result = keep value ensures result === value *)
end

module First = Keep (Options)
module Second = Keep (Options)
module Alias = First

module Marked (Container : CONTAINER) () = struct
  type marker = Marker

  let marker () = Marker
  (*@ result = marker () ensures result === Marker *)

  let keep value = Container.keep value
  (*@ result = keep value ensures result === value *)
end

module With_layout = Marked (Options) ()

module type LISTS = sig
  type 'a t = 'a list

  val keep : 'a t -> 'a t
  (*@ result = keep value ensures result === value *)
end

module Lists = struct
  type 'a t = 'a list

  let keep (value : 'a t) = value
  (*@ result = keep value ensures result === value *)
end

module Keep_list (Container : LISTS) = struct
  let keep value = Container.keep value
  (*@ result = keep value ensures result === value *)
end

module List_client = Keep_list (Lists)

let clients () =
  assert (First.keep (Some 17) = Some 17);
  assert (Second.keep (Some true) = Some true);
  assert (Alias.keep (None : int Options.t) = None);
  assert (With_layout.keep (Some 23) = Some 23);
  assert (With_layout.marker () = With_layout.Marker);
  assert (List_client.keep [ 17; 23 ] = [ 17; 23 ]);
  assert (List_client.keep [ true; false ] = [ true; false ]);
  let value = ref 7 in
  match First.keep (Some value) with
  | None -> assert false
  | Some result ->
      assert (result == value);
      result := 11;
      assert (!value = 11)
