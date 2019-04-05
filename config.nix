{
  packageOverrides = pkgs: {
    haskellPackages = pkgs.haskell.packages.ghc843.override {
      overrides = haskellPackagesNew: haskellPackagesOld: {
        cardano-prelude     = haskellPackagesNew.callPackage ./cardano-prelude.nix {};
        canonical-json      = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});

        # Pain in the ass
        iohk-monitoring     = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./iohk-monitoring.nix {
          libyaml           = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./libyaml.nix {});
        });

        contra-tracer        = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./iohk-monitoring-contra-tracer.nix { });

        cardano-sl-x509     = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./cardano-sl-x509.nix { });

        # Dependency from 
        quickcheck-classes  = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callHackage "quickcheck-classes" "0.4.14.3" {});

        stack-hpc-coveralls = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./stack-hpc-coveralls.nix {});

        cardano-shell       = haskellPackagesNew.callPackage ./cardano-shell.nix { };
      };
    };
  };
}
