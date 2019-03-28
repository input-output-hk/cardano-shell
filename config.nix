{
  packageOverrides = pkgs: {
    haskellPackages = pkgs.haskell.packages.ghc843.override {
      overrides = haskellPackagesNew: haskellPackagesOld: {
        cardano-prelude   = haskellPackagesNew.callPackage ./cardano-prelude.nix {};
        canonical-json    = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});

        # Pain in the ass
        iohk-monitoring   = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./iohk-monitoring.nix { 
          libyaml           = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./libyaml.nix {});
        });

        basic-tracer      = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./iohk-monitoring-basic-tracer.nix { });

        cardano-sl-x509   = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./cardano-sl-x509.nix { });

        cardano-shell     = haskellPackagesNew.callPackage ./cardano-shell.nix { };
        stack-hpc-coveralls = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./stack-hpc-coveralls.nix {});
      };
    };
  };
}
