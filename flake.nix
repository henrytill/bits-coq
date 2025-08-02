{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    rocq-opam = {
      url = "github:rocq-prover/opam";
      flake = false;
    };
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.opam-repository.follows = "opam-repository";
    };
    flake-utils = {
      follows = "opam-nix/flake-utils";
    };
    rocq-stdlib-patch = {
      url = "https://github.com/rocq-prover/stdlib/commit/1b6680355e40b9a05c288ad900e0060090f05a6d.diff";
      flake = false;
    };
  };
  nixConfig = {
    extra-substituters = [ "https://henrytill.cachix.org" ];
    extra-trusted-public-keys = [
      "henrytill.cachix.org-1:EOoUIk8e9627viyFmT6mfqghh/xtfnpzEtqT4jnyn1M="
    ];
  };
  outputs =
    {
      self,
      flake-utils,
      opam-nix,
      nixpkgs,
      opam-repository,
      rocq-opam,
      rocq-stdlib-patch,
      ...
    }@inputs:
    let
      package = "bits-rocq";
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        repos = [
          "${opam-repository}"
          "${rocq-opam}/released"
        ];
        on = opam-nix.lib.${system};
        scope =
          on.buildOpamProject
            {
              inherit repos;
              resolveArgs.with-test = true;
            }
            package
            ./.
            {
              ocaml-base-compiler = "5.3.0";
            };
        overlay =
          final: prev:
          let
            rocqLib = "${prev.rocq-stdlib}/lib/ocaml/${prev.ocaml.version}/site-lib/coq";
            rocqLibConfig = {
              preConfigure = ''
                export ROCQLIB=${rocqLib}
              '';
            };
          in
          {
            rocq-stdlib = prev.rocq-stdlib.overrideAttrs (as: {
              patches = as.patches ++ [ rocq-stdlib-patch ];
            });
            coq-menhirlib = prev.coq-menhirlib.overrideAttrs (as: rocqLibConfig // { });
            ${package} = prev.${package}.overrideAttrs (as: rocqLibConfig // { });
          };
      in
      {
        legacyPackages = scope.overrideScope overlay;
        packages.default = self.legacyPackages.${system}.${package};
      }
    );
}
