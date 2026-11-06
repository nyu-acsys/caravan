module type S = Stack_intf.S

module Test (Stack : S) = struct
  let drain (st : 'a Stack.t) : 'a list =
    let rec loop () =
      match Stack.pop st with None -> [] | Some v -> v :: loop ()
    in
    loop ()
end

module Saturn_stack = struct
  type 'a t = 'a Treiber_stack.t

  let create () = Treiber_stack.create ()
  let push st value = Treiber_stack.push st value
  let pop st = Treiber_stack.pop_opt st
end

module Client = Test (Saturn_stack)

let drain stack = Client.drain stack
