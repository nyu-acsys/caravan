let identity (x : int) = x
(*@ result = identity x requires Map.get x ensures Map.get result *)
