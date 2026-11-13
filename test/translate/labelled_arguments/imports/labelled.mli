val keep : value:'a -> tag:int -> 'a

(*@ result = keep value tag ensures result === value *)
val optional : ?value:int -> unit -> int
(*@ result = optional value token ensures true *)
