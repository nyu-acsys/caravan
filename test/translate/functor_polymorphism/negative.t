A polymorphic actual operation must establish the requested module contract.

  $ ! caravan --shh wrong_contract.ml > rejected.out 2>&1
  $ grep 'Verification Error:' rejected.out
  Verification Error: The module argument does not establish this view's postcondition.
  $ ! grep -Eq 'Internal Error:|Unsupported Error:|timed out' rejected.out

Raising module arguments report the current forwarding limitation at the source.

  $ ! caravan --shh raising_unsupported.ml > raising.out 2>&1
  $ grep 'Unsupported Error:' raising.out
  Unsupported Error: A raising operation in a checked module binding is not supported yet.
  $ ! grep -q 'Internal Error:' raising.out

Specialized checked bindings reject polymorphic operations at the source.

  $ ! caravan --shh nested_specialization.ml > nested.out 2>&1
  $ grep 'Unsupported Error:' nested.out
  Unsupported Error: A polymorphic operation in a specialized checked module binding is not supported yet.
  $ ! grep -q 'Internal Error:' nested.out

Polymorphic checked views cannot yet be forwarded through another checked view.

  $ ! caravan --shh chained_unsupported.ml > chained.out 2>&1
  $ grep 'Unsupported Error:' chained.out
  Unsupported Error: A polymorphic operation forwarded through a previously checked module view is not supported yet.
  $ ! grep -q 'Internal Error:' chained.out
