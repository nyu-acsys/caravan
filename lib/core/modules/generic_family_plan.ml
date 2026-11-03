(** Stable worker assignments used when mutually dependent declarations share a family. *)

open Base

type t = {
  runtime : (Ident.t * string) list;
  proofs : (string * string) list;
  assets : (string * string) list;
}

let empty = { runtime = []; proofs = []; assets = [] }

let runtime plan id proposed =
  Option.value (List.Assoc.find plan.runtime id ~equal:Ident.same) ~default:proposed

let proof plan key proposed =
  Option.value (List.Assoc.find plan.proofs key ~equal:String.equal) ~default:proposed

let asset plan key proposed =
  Option.value (List.Assoc.find plan.assets key ~equal:String.equal) ~default:proposed
