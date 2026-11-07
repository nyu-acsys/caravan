module Container = struct
  let identity (value : int) = value
end

(*@ result = identity value ensures result = value *)
