{ pkgs ? import <nixpkgs> { } }:
pkgs.mkShell {
  name = "software-foundations";
  packages = with pkgs; [ gnumake coq_8_13 vscodium ];
}
