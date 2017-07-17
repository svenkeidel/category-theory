{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  name = "categories";
  version = "0.0.1";
  src = ./.;
  buildInputs = with pkgs; [
    coq_8_6
  ];
}
