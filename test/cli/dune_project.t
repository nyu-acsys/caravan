Discover interface contracts from the containing Dune stanza and its transitive
libraries, including libraries with implementations, without compiling the project.

  $ python3 check_dune_project.py
  Dune discovery verifies transitive source contracts without an explicit include path.
  Editor dependencies include project configuration; unrelated libraries stay excluded.
  Standalone mode and explicit interface overrides remain available.
  Nested projects use their enclosing workspace without confusing same-named libraries.
  Generated interfaces remain available while Dune holds the project build lock.
