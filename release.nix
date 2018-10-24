let
   config = {
    packageOverrides = pkgs: rec {
      haskellPackages = pkgs.haskell.packages.ghc843.override {
        overrides = haskellPackagesNew: haskellPackagesOld: rec {
          universum         = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callHackage "universum" "1.3.0" {});
          cardano-shell     = haskellPackagesNew.callPackage ./cardano-shell.nix { };
        };
      };
    };
  };

  # pinning
  fetchNixPkgs  = import ./scripts/nix/fetch-nixpkgs.nix;
  pkgs          = import fetchNixPkgs { inherit config; };
 in
  { cardano-shell = pkgs.haskellPackages.cardano-shell;
  }
