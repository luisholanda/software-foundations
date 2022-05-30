{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs { inherit system; config.allowUnfree = true; };
    in {
      devShells.default = pkgs.mkShell {
        name = "software-foundations";

        packages = with pkgs; [
          coq
          (vscode-with-extensions.override {
            vscode = vscodium;
          })
        ];
      };
    });
}
