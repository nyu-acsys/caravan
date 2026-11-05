Constructor initializers in outlines retain automatic invariant establishment and
support both preceding pure bindings and bindings inside the initializer.

  $ caravan --shh initializers.ml
  Verification successful.

Initializer outlines are also available to editor hints and proof views.

  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only initializers.ml > initializers.json
  $ python3 -c 'import json; r = json.load(open("initializers.json")); steps = [a for a in r["annotations"] if a["kind"] == "ProofStep"]; assert len(steps) == 2; assert all(a["text"].startswith("initially") for a in steps)'
