let claim (a : int ref) (b : int ref) = ()
(*@ claim a b
    requires own a.contents 0 && own b.contents 0
    ensures a = b *)
