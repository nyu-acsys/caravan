module type S = Stack_intf.S

module Test (Stack : S) = struct
  (** Work done by a single domain. The first argument is the domain identifier *)
  let work (id : int) (st : 'a Stack.t) : unit =
    for i = 0 to 9 do
      Stack.push st id
    done

  (** Functions to use to inspect sequentially the content of the stack *)
  let drain (st : 'a Stack.t) : 'a list =
    let rec loop () =
      match Stack.pop st with None -> [] | Some v -> v :: loop ()
    in
    loop ()

  (** The test function returns the number of elements in the stack and its contents *)
  let test () : int * 'a list =
    let st = Stack.create () in
    let domainA = Domain.spawn (fun () -> work 1 st) in
    let domainB = Domain.spawn (fun () -> work 2 st) in
    Domain.join domainA;
    Domain.join domainB;
    let content = drain st in
    (List.length content, content)
end

module Saturn_stack = struct
  type 'a t = 'a Treiber_stack.t

  let create () = Treiber_stack.create ()
  let push st value = Treiber_stack.push st value
  let pop st = Treiber_stack.pop_opt st
end

module Client = Test (Saturn_stack)

let drain stack = Client.drain stack

let test () = Client.test ()
