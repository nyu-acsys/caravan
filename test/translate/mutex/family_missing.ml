type 'a t = { mutable value : 'a }

let signal condition = Condition.signal condition
