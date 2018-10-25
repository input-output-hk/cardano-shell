let

  config = {
    packageOverrides = pkgs: rec {
      
      haskellPackages = pkgs.haskell.packages.ghc843.override {
        overrides = haskellPackagesNew: haskellPackagesOld: rec {

          cardano-prelude   = haskellPackagesNew.callPackage ./cardano-prelude.nix {
            # Oh yeah, let there be pain.
            # Fails when building canonical-json-0.5.0.0.drv.
            canonical-json = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});
            containers     = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callHackage "containers" "0.5.11.0" {});
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
