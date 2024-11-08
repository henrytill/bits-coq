(lang dune 3.16)

(using coq 0.8)

(using menhir 2.1)

(name coq_bits)

(generate_opam_files true)

(source
 (github henrytill/coq_bits))

(authors "Henry Till <henrytill@gmail.com>")

(maintainers "Henry Till <henrytill@gmail.com>")

(package
 (name coq_bits)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune menhir coq coq-menhirlib)
 (tags
  (topics "to describe" your project)))
