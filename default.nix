{ pkgs ? import <nixpkgs> {} }:

let
  texEnv = pkgs.texlive.combine {
      inherit (pkgs.texlive) scheme-small latexmk pgf tikz-cd;
  };
  
  hsEnv = pkgs.haskellPackages.ghcWithPackages(p: with p; [
    Cabal cabal-install hlint comonad
  ]);

in pkgs.stdenv.mkDerivation {
  name = "categories";
  version = "0.0.1";
  src = ./.;
  buildInputs = [
    texEnv hsEnv
  ];
}
