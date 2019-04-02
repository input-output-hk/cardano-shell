{ config ? {}
, system ? builtins.currentSystem
, iohkLib ? import ./nix/iohk-common.nix { inherit config system; application = "cardano-sl"; }
, pkgs ? iohkLib.pkgs
, gitrev ? iohkLib.commitIdFromGitRepo ./.
}:

let
  haskell = iohkLib.nix-tools.haskell { inherit pkgs; };

  pkgSet = haskell.mkStackPkgSet {
    stack-pkgs = import ./nix/pkgs.nix;
    pkg-def-extras = [];
    modules = [ {
      packages.cardano-shell.src = iohkLib.cleanSourceHaskell ./.;
    } ];
  };
  haskellPackages = pkgSet.config.hsPkgs;

in {
  inherit haskellPackages iohkLib;

  inherit (haskellPackages.cardano-shell.components)
    all benchmarks exes library tests;
}
