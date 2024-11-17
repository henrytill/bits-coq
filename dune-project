(lang dune 3.16)

(using coq 0.8)

(using menhir 2.1)

(name bits-coq)

(generate_opam_files true)

(source
 (github henrytill/bits-coq))

(authors "Henry Till <henrytill@gmail.com>")

(maintainers "Henry Till <henrytill@gmail.com>")

(package
 (name bits-coq)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  menhir
  coq
  coq-menhirlib
  (ppx_deriving
   (and
    :with-test
    (>= 6.0.3)))
  (ppx_import
   (and
    :with-test
    (>= 1.11.0)))
  (alcotest
   (and
    :with-test
    (>= 1.7.0))))
 (tags
  (topics "to describe" your project)))
