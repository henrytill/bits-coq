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
    coq-stdlib-src = {
      url = "github:rocq-prover/stdlib";
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
      coq-stdlib-src,
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
        overlay = final: prev: {
          coq-stdlib = final.callPackage (on.opam2nix {
            src = coq-stdlib-src;
            name = "coq-stdlib";
          }) { };
          ${package} = prev.${package}.overrideAttrs (as: { });
        };
      in
      {
        legacyPackages = scope.overrideScope overlay;
        packages.default = self.legacyPackages.${system}.${package};
      }
    );
}
