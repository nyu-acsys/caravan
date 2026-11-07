module Checked : Actual.Ordinary = Actual.First

let client (x : Checked.t) = ()
(*@ client x requires view_checked_0.counter x 0 *)
