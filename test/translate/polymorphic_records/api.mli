type 'a t

(*@ predicate contents (cell : 'a t) (value [@implicit] : 'a) *)
val make : 'a -> 'a t

(*@ cell = make value ensures contents cell value *)
val read : 'a t -> 'a

(*@ result = read cell requires contents cell stored
    ensures contents cell stored && result === stored *)
val write : 'a t -> 'a -> unit
(*@ write cell value requires contents cell before ensures contents cell value *)
