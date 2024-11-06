(lang dune 3.16)

(using coq 0.8)

(using menhir 2.1)

(name coq_bits)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name coq_bits)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune menhir coq coq-menhirlib)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
