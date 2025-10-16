{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "ghc";
  buildInputs = with pkgs; [ ghc ];
}
