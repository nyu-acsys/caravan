(lang dune 3.12)
(using menhir 2.1)

(generate_opam_files)

(source (github nyu-acsys/caravan))

(authors "Thomas Wies")

(maintainers "Thomas Wies")

(license MIT)

(package
 (name caravan)
 (synopsis "Verifier of multicore OCaml programs, built on Raven")
 (description "Caravan verifies multicore OCaml programs by translating them, with their specifications, to the Raven verifier.")
 (depends
  (ocaml
   (>= 5.5.0))
  (dune
   (>= 3.12))
  (raven-ivl
   (>= 1.5.0))
  (menhir
   (and
    :build
    (>= 20220210)))
  (ocamlformat
   (and
    :with-dev-setup
    (>= 0.29.0)))
  (base
   (>= 0.14))
  (stdio
   (>= 0.14))
  (logs
   (>= 0.7.0))
  (fmt
   (>= 0.9.0))
  (cmdliner
   (>= 1.2.0))))
