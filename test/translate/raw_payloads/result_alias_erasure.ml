module Producer = struct
  let forward value = value
end

module Public : sig
  val alias : 'a -> 'a
end = struct
  let alias = Producer.forward
end
