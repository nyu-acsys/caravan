The runtime interleaving exposes stale-capacity refresh after counter wrap. This
fixture models signed 3-bit arithmetic by shadowing integer addition and
subtraction in the copied source; it is not native word-size verification.

  $ cat wrap_prefix.ml bounded_queue.ml > runtime.ml
  $ sed '/let capacity = get_capacity old_tail in/a\
  > \  after_capacity ();' runtime.ml > runtime.ml.edited
  $ mv runtime.ml.edited runtime.ml
  $ cat wrap_harness.ml >> runtime.ml
  $ sed '/^    else match get_next old_tail with$/,/^    | Link (Node _ as next) -> push_as t new_node next mono$/c\
  > \    else match mono with Unit -> raise Full | Bool -> false' runtime.ml > runtime_original.ml
  $ ocamlopt -o runtime_original.exe runtime_original.ml
  $ ./runtime_original.exe
  Bool wrapper: target=full; queued_target=false
  Unit wrapper: target=full; queued_target=false
  genuine full capacity=2: Bool=false; Unit=Full
  capacity=0: Bool=false; Unit=Full
  of_list_exn: capacity=1 full/rejected; FIFO=ok; empty=ok; spare capacity=ok; oversize=Full; capacity=0=Full
  summary: Bool=full/false; Unit=full/false; model=signed 3-bit [-4,3]
  $ ocamlopt -o runtime.exe runtime.ml
  $ ./runtime.exe
  Bool wrapper: target=pushed; queued_target=true
  Unit wrapper: target=pushed; queued_target=true
  genuine full capacity=2: Bool=false; Unit=Full
  capacity=0: Bool=false; Unit=Full
  of_list_exn: capacity=1 full/rejected; FIFO=ok; empty=ok; spare capacity=ok; oversize=Full; capacity=0=Full
  summary: Bool=pushed/true; Unit=pushed/true; model=signed 3-bit [-4,3]
  $ sed -e 's/~capacity:(capacity - len) ~counter:len Null/~capacity:(capacity - len - 1) ~counter:len Null/' -e 's/(len - 1, capacity - len + 1, tail)/(len - 1, capacity - len, tail)/' runtime.ml > runtime_constructor_original.ml
  $ ocamlopt -o runtime_constructor_original.exe runtime_constructor_original.ml
  $ ./runtime_constructor_original.exe constructor-original
  capacity=1 old cache initializers: Bool=true; Unit=pushed; lengths=2/2
