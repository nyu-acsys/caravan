module Cell = struct
  let create () =
    let cell =
      Atomic.make 0
      (*@ initializes [Ghost.init value 0;
          Ghost.init facts (Authority.full (Facts.set Set.empty))] *)
    in
    (*@ lemma publish cell *)
    cell
  (*@ result = create ()
      ensures own result 0
      ensures own (Ghost.at value result) 0
      ensures own (Ghost.at facts result) (Authority.full (Facts.set (Set.singleton 1))) *)
end

module Alias = Cell

let client () = Alias.create ()
(*@ result = client ()
    ensures own result 0
    ensures own (Ghost.at Alias.value result) 0
    ensures own (Ghost.at Alias.facts result)
      (Alias.Authority.full (Alias.Facts.set (Set.singleton 1))) *)
