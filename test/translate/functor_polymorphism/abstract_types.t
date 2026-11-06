Abstract type constructors preserve their value dictionaries through generic operations,
including repeated instances, aliases, and a generative result layout. Parameterized
manifest aliases expand to the existing list encoding.

  $ caravan --shh abstract_types.ml
  Verification successful.
  $ caravan --shh --emit-rav abstract_types.ml > abstract_types.rav
  $ raven --shh abstract_types.rav
  Verification successful.

The body datatype uses a World with an abstract type-constructor factory.

  $ grep -q 'World_.*\[Type_t' abstract_types.rav
