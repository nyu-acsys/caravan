Generic atomic ghost inputs and outputs retain their types in native named functors,
repeated applications, aliases, and distinct applications.

  $ caravan --shh au_functor.ml
  Verification successful.
  $ caravan --shh --emit-rav au_functor.ml > au_functor.rav
  $ raven --shh au_functor.rav
  Verification successful.
