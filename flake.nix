{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    coq-opam = {
      url = "github:coq/opam";
      flake = false;
    };
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.opam-repository.follows = "opam-repository";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
      follows = "opam-nix/flake-utils";
    };
  };
  outputs =
    {
      self,
      flake-utils,
      opam-nix,
      nixpkgs,
      opam-repository,
      coq-opam,
      ...
    }@inputs:
    let
      package = "bits-coq";
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        repos = [
          "${opam-repository}"
          "${coq-opam}/released"
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
              ocaml-base-compiler = "5.2.0";
              coq = "*";
            };
        overlay = final: prev: { ${package} = prev.${package}.overrideAttrs (as: { }); };
      in
      {
        legacyPackages = scope.overrideScope overlay;
        packages.default = self.legacyPackages.${system}.${package};
      }
    );
}
