module Stack = Treiber_stack

module Test = struct
  let rec drain stack =
    match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
  (*@ result = drain stack
      requires Stack.stack stack xs
      ensures Stack.stack stack [] && result = [] *)
end
