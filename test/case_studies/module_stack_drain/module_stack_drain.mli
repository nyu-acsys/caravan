module Stack = Treiber_stack

module Test : sig
  val drain : Stack.t -> int list
  (*@ result = drain stack
      requires Stack.stack stack xs
      ensures Stack.stack stack [] && result = xs *)
end
