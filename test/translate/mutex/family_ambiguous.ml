type 'a t = { mutable value : 'a }

let signal (_first : int t) (_second : bool t) condition = Condition.signal condition
