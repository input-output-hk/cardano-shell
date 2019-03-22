{
  packageOverrides = pkgs: {
    haskellPackages = pkgs.haskell.packages.ghc843.override {
      overrides = haskellPackagesNew: haskellPackagesOld: {
        cardano-prelude   = haskellPackagesNew.callPackage ./cardano-prelude.nix {};
        canonical-json    = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});


        libyaml           = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./libyaml.nix {});
        iohk-monitoring   = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./iohk-monitoring.nix { });

        basic-tracer      = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./iohk-monitoring-basic-tracer.nix { });
        cardano-shell     = haskellPackagesNew.callPackage ./cardano-shell.nix { };
        stack-hpc-coveralls = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./stack-hpc-coveralls.nix {});
      };
    };
  };
}
