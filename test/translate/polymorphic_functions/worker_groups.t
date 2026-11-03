Polymorphic functions share a functor when they use each other at their own type
parameters; nested calls wrap at another type, so it applies the shared functor.

  $ caravan --shh worker_groups.ml
  Verification successful.
  $ caravan --shh --emit-rav worker_groups.ml > worker_groups.rav
  $ grep -E '^module [A-Za-z_0-9]+\[|= *[A-Za-z_0-9.]+\[' worker_groups.rav
  module Ocaml_ListValue_1[E: Ocaml_Value_1] : Ocaml_Value_1
    rep type Carrier = Library.List[E.Carrier]
  module Generic[A0: Ocaml_Value_1]
    module Values_A0List_1 : Ocaml_ListValue_1 = Ocaml_ListValue_1[Generic.A0]
  module Poly_nested_1[A0: Ocaml_Value_1]
    module Poly_Instance_0_1 : Generic = Generic[Poly_nested_1.A0]
    module Poly_Instance_1_1 : Generic = Generic[Poly_nested_1.Values_A0List_1]
  module Poly_Instance_2_1 : Generic = Generic[Ocaml_IntValue_1]
  $ raven --shh worker_groups.rav
  Verification successful.
