open Base
module C = Caravan_core
module W = C.Worker_groups

let worker name = W.{ name; arity = 1; witness = false }
let use namespace target = W.{ namespace; target; arguments = None }

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let () =
  let drain = worker "Outer.Drain" in
  let sibling = worker "Outer.Sibling" in
  let nodes = [ W.Generic_module "Outer"; W.Worker drain; W.Worker sibling ] in
  let uses =
    [
      use [ "Outer" ] "Outer.Drain"; use [ "Outer"; "Drain" ] "Outer.Parameter.Poly$stack";
    ]
  in
  let edges = W.weighted_uses ~applications:[] nodes uses in
  assert (not (Map.mem edges drain.name));
  assert (
    List.Assoc.find_exn (Map.find_exn edges "Outer") drain.name ~equal:String.equal = 1);
  let groups =
    get (W.create ~generic_modules:[ "Outer" ] ~applications:[] [ drain; sibling ] uses)
  in
  assert (List.equal (List.equal String.equal) groups [ [ drain.name; sibling.name ] ]);
  let uses = uses @ [ use [ "Outer"; "Drain" ] "Outer.Sibling.member" ] in
  let edges = W.weighted_uses ~applications:[] nodes uses in
  assert (
    List.Assoc.find_exn (Map.find_exn edges drain.name) sibling.name ~equal:String.equal
    = 1);
  assert (
    List.is_empty
      (get
         (W.create ~generic_modules:[ "Outer" ] ~applications:[] [ drain; sibling ] uses)))

let () =
  let nested = worker "Outer.Nested.Worker" in
  let nodes =
    [ W.Generic_module "Outer"; W.Generic_module "Outer.Nested"; W.Worker nested ]
  in
  let edges =
    W.weighted_uses ~applications:[] nodes
      [ use [ "Outer"; "Nested"; "Worker" ] "Outer.Parameter.resource" ]
  in
  assert (Map.is_empty edges)

let () =
  let child = worker "Outer.Child" in
  let uses =
    [ use [ "Outer" ] child.name; use [ "Outer"; "Child" ] "AppliedOther.member" ]
  in
  match
    W.create ~generic_modules:[ "Outer" ]
      ~applications:[ ("AppliedOther", "Outer") ]
      [ child ] uses
  with
  | Error _ -> ()
  | Ok _ ->
      failwith "An application of the parent at other arguments remains a dependency"
