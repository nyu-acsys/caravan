let drop_head (xs : int list) = match xs with [] -> [] | _ :: tail -> tail
(*@ result = drop_head xs pure *)

let check_assoc (a : int list) (b : int list) (c : int list) =
  (*@ lemma append_assoc a b c *)
  ()
(*@ check_assoc a b c
    ensures (a @ b) @ c = a @ (b @ c) *)
