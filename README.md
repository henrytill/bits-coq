# bits-rocq

[![CI](https://github.com/henrytill/bits-rocq/actions/workflows/ci.yml/badge.svg)](https://github.com/henrytill/bits-rocq/actions/workflows/ci.yml)

Creating a local opam switch for this project:

```sh
opam switch create ./ ocaml-system --repos default,rocq-released=https://rocq-prover.org/opam/released  --deps-only --with-test
```
