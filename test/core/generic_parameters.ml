open Base
(** Recorded quantifiers survive compiler levels without generalizing weak variables. *)

module G = Caravan_core.Generic_parameters

let get = function
  | Ok value -> value
  | Error error -> failwith error.Caravan_core.Report.message

let () =
  let quantified = Btype.newgenty (Types.Tvar (Some "a")) in
  let weak = Ctype.newvar () in
  let worker =
    get
      (G.discover ~key:"resource" ~name:"Resource" ~at:Location.none ~explicit:2
         [ quantified; weak ])
  in
  assert (List.length worker.variables = 1);
  Types.set_level quantified 42;
  let rebound =
    get (G.rebind ~expand:Fn.id ~at:Location.none worker [ quantified; weak ])
  in
  assert (List.equal Types.eq_type rebound.variables [ quantified ]);
  let arguments =
    get
      (G.instantiate ~expand:Fn.id ~at:Location.none rebound
         [ Some Predef.type_int; Some weak ])
  in
  assert (List.equal Types.eq_type arguments [ Predef.type_int ]);
  assert (
    Result.is_error
      (G.instantiate ~expand:Fn.id ~at:Location.none rebound
         [ Some Predef.type_int; Some Predef.type_bool ]));
  assert (Result.is_error (G.rebind ~expand:Fn.id ~at:Location.none worker [ weak; weak ]));
  let extra = Btype.newgenty (Types.Tvar (Some "b")) in
  assert (
    Result.is_error
      (G.rebind ~expand:Fn.id ~at:Location.none worker [ quantified; extra ]))

let () =
  let a = Btype.newgenty (Types.Tvar (Some "a")) in
  let b = Btype.newgenty (Types.Tvar (Some "b")) in
  let weak = Ctype.newvar () in
  let worker =
    get (G.discover ~key:"pair" ~name:"Pair" ~at:Location.none ~explicit:3 [ a; b; weak ])
  in
  Types.set_level a 42;
  let c = Btype.newgenty (Types.Tvar (Some "c")) in
  let d = Btype.newgenty (Types.Tvar (Some "d")) in
  assert (Result.is_error (G.rebind ~expand:Fn.id ~at:Location.none worker [ a; c; d ]))
