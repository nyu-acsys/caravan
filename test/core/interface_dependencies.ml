open Base
module D = Caravan_core.Interface_dependencies

let signature text =
  Lexer.init ();
  Parse.interface (Lexing.from_string text)

let order entries =
  D.order entries ~name:fst
    ~signature:(fun (_, text) -> signature text)
    ~at:(fun _ -> Location.none)

let names = Result.map ~f:(List.map ~f:fst)

let () =
  assert (
    Poly.equal
      (names
         (order
            [
              ("Queue", "include Queue_intf.S");
              ("Queue_intf", "module type S = sig type t end");
            ]))
      (Ok [ "Queue_intf"; "Queue" ]));
  assert (
    Poly.equal
      (names
         (order
            [
              ("A", "val f : int -> int");
              ("B", "module type S = sig end");
              ("C", "include B.S");
            ]))
      (Ok [ "A"; "B"; "C" ]));
  assert (
    Poly.equal
      (names
         (order
            [
              ("A", "module Local : sig module type S = sig end end include Local.S");
              ("Local", "include A.S");
            ]))
      (Ok [ "A"; "Local" ]));
  assert (Result.is_error (order [ ("A", "include B.S"); ("B", "include A.S") ]));
  Depend.free_structure_names := Depend.String.Set.singleton "Existing";
  let _ = order [ ("A", "include B.S"); ("B", "module type S = sig end") ] in
  assert (
    Depend.String.Set.equal !Depend.free_structure_names
      (Depend.String.Set.singleton "Existing"));
  Depend.free_structure_names := Depend.String.Set.empty
