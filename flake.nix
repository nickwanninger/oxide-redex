{
  description = "Racket Playground for Dynamics";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in with pkgs; {
          devShell = mkShell {
            buildInputs = [ racket ];
          };
        });
}
