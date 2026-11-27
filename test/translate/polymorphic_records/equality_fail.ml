type 'a t = { mutable value : 'a }

let compare (left : 'a t) right = left = right
