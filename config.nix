{
  packageOverrides = pkgs: {
    haskellPackages = pkgs.haskell.packages.ghc843.override {
      overrides = haskellPackagesNew: haskellPackagesOld: {
        cardano-prelude   = haskellPackagesNew.callPackage ./cardano-prelude.nix {};
        canonical-json    = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});

        iohk-monitoring   = haskellPackagesNew.callPackage ./iohk-monitoring.nix { };
        cardano-shell     = haskellPackagesNew.callPackage ./cardano-shell.nix { };
        stack-hpc-coveralls = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./stack-hpc-coveralls.nix {});
      };
    };
  };
}
