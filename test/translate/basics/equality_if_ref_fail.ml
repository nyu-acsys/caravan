let claim (choose : bool) (a : int ref) (b : int ref) = ()
(*@ claim choose a b requires (if choose then a else b) = a *)
