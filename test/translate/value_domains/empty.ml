type empty = |

let absurd (value : empty) : int = match value with _ -> .

(*@ result = absurd value pure *)
let empty_list () : empty list = []
(*@ result = empty_list () ensures result === [] *)

let quantified () = ()
(*@ quantified () ensures forall value : empty. false *)
