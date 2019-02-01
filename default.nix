{ config ? {}
, system ? builtins.currentSystem
, iohkLib ? import ./nix/iohk-common.nix { inherit config system; application = "cardano-sl"; }
, pkgs ? iohkLib.pkgs
, gitrev ? iohkLib.commitIdFromGitRepo ./.
}:

let
  haskellPackages = import ./nix/pkgs.nix {
    inherit pkgs;
    src = iohkLib.cleanSourceHaskell ./.;
  };

in {
  inherit haskellPackages;

  inherit (haskellPackages.cardano-shell.components)
    benchmarks exes library tests;
}
