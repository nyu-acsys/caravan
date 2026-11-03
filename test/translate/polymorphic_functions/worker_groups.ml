let wrap value = [ value ]
(*@ result = wrap value pure ensures result === [ value ] *)

let single value = wrap value
(*@ result = single value pure ensures result === [ value ] *)

let nested value = wrap (wrap value)
(*@ result = nested value pure ensures result === [ [ value ] ] *)

let flat (value : int) = single value
(*@ result = flat value ensures result === [ value ] *)
