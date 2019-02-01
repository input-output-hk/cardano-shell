############################################################################
# Hydra release jobset
#
# Example build for Linux:
#
#   nix-build release.nix -A exes.cardano-shell-exe.x86_64-linux
#
############################################################################

let
  iohkLib = import ./nix/iohk-common.nix { application = "cardano-sl"; };
  fixedNixpkgs = iohkLib.pkgs;

in { supportedSystems ? [ "x86_64-linux" ]
  , scrubJobs ? true
  , cardano-shell ? { outPath = ./.; rev = "abcdef"; }
  , nixpkgsArgs ? {
      config = (import ./nix/config.nix // { allowUnfree = false; inHydra = true; });
      gitrev = cardano-shell.rev;
    }
  }:

with (import (fixedNixpkgs.path + "/pkgs/top-level/release-lib.nix") {
  inherit supportedSystems scrubJobs nixpkgsArgs;
  packageSet = import cardano-shell.outPath;
});

let
  jobs = mapTestOn {
    exes.cardano-shell-exe = supportedSystems;
  };

in
  jobs
