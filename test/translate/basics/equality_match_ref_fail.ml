let claim (choose : bool) (a : int ref) (b : int ref) = ()
(*@ claim choose a b requires (match choose with true -> a | false -> b) = a *)
