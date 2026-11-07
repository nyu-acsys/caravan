Nested resources and ghost fields remain usable inside a sealed module.

  $ caravan --shh nested_assets.ml
  Verification successful.
  $ caravan --shh --emit-rav nested_assets.ml > nested_assets.rav
  $ raven --shh nested_assets.rav
  Verification successful.

Aliases of the same descriptor cannot initialize a field twice.

  $ cp nested_assets.ml nested_assets_duplicate_fail.ml
  $ caravan --shh nested_assets_duplicate_fail.ml 2>&1 | grep -F 'Type Error: A ghost field is initialized more than once.'
  Type Error: A ghost field is initialized more than once.

A containing signature keeps implementation fields private from clients.

  $ cp nested_assets.ml nested_assets_hidden_fail.ml
  $ caravan --shh nested_assets_hidden_fail.ml 2>&1 | grep -F 'Type Error: Unknown or inaccessible ghost field.'
  Type Error: Unknown or inaccessible ghost field.

Resource instances with different functor arguments retain distinct types.

  $ cp nested_assets.ml nested_assets_wrong_instance_fail.ml
  $ caravan --shh nested_assets_wrong_instance_fail.ml 2>&1 | grep -F 'Type Error: This expression has type Sibling_authority.t'
  Type Error: This expression has type Sibling_authority.t

A descriptor also retains its owner type.

  $ cp nested_assets.ml nested_assets_wrong_owner_fail.ml
  $ caravan --shh nested_assets_wrong_owner_fail.ml 2>&1 | grep -F 'Type Error: This ghost field has a different owner type.'
  Type Error: This ghost field has a different owner type.
