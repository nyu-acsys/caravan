type 'a t = { values : 'a list }

let identity (value : 'a t) = value
(*@ result = identity value pure ensures result === { values = [0] } *)
