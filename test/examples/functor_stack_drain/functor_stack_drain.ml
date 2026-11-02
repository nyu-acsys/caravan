module type STACK = sig
  type t

  (*@ predicate stack (t : t) (xs [@implicit] : int list) *)
  val pop_opt : t -> int option
  (*@ result = atomic pop_opt t
      atomic requires stack t xs
      atomic ensures match xs with
        | [] -> result = None && stack t []
        | x :: xs' -> result = Some x && stack t xs' *)
end

module Test (Stack : STACK) = struct
  let rec drain stack =
    match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
  (*@ result = drain stack
      requires Stack.stack stack xs
      ensures Stack.stack stack [] && result = xs *)
end

module Integer_stack = struct
  type t = int Treiber_stack.t

  let pop_opt (t : t) = Treiber_stack.pop_opt t
  (*@ Ghost.scope (fun step ->
      let token = Pop.bind () in
      let xs = Pop.access token t in
      unfold stack t xs;
      let result = step () in
      fold stack t (match xs with [] -> [] | _ :: rest -> rest);
      Pop.commit token t result;
      result) *)
  (*@ manual *)
  (*@ result = atomic pop_opt t
      atomic requires stack t xs
      atomic ensures match xs with
        | [] -> result = None && stack t []
        | x :: xs' -> result === Some x && stack t xs' *)
end

module Client = Test (Integer_stack)

let drain stack = Client.drain stack
(*@ Ghost.scope (fun step ->
    fold Integer_stack.stack stack xs;
    let result = step () in
    unfold Integer_stack.stack stack [];
    result) *)
(*@ manual *)
(*@ result = drain stack
    requires Treiber_stack.stack stack xs
    ensures Treiber_stack.stack stack [] && result = xs *)
