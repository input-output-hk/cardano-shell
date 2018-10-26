let

  config = {
    packageOverrides = pkgs: rec {

      haskellPackages = pkgs.haskell.packages.ghc844.override {
        overrides = haskellPackagesNew: haskellPackagesOld: rec {

          cardano-prelude   = haskellPackagesNew.callPackage ./cardano-prelude.nix {
            canonical-json = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});
          };

          cardano-shell     = haskellPackagesNew.callPackage ./cardano-shell.nix {
          };

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
