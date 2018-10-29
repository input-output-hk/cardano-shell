let
   config = {
    packageOverrides = pkgs: rec {
      haskellPackages = pkgs.haskell.packages.ghc843.override {
        overrides = haskellPackagesNew: haskellPackagesOld: rec {
          cardano-prelude   = haskellPackagesNew.callPackage ./cardano-prelude.nix {
            #canonical-json = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callHackage "canonical-json" "0.5.0.1" {});
            canonical-json = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callPackage ./canonical-json.nix {});
          };
          cardano-shell     = haskellPackagesNew.callPackage ./cardano-shell.nix { };
        };
      };
    };
  };
  nixpkgs = builtins.fetchTarball {
    url    = "https://github.com/NixOS/nixpkgs/archive/069bf7aee30faf7b3ed773cfae2154d761b2d6c2.tar.gz";
    sha256 = "1c44vjb60fw2r8ck8yqwkj1w4288wixi59c6w1vazjixa79mvjvg";
  };

  pkgs = import nixpkgs { inherit config; };
in
  { cardano-shell = pkgs.haskellPackages.cardano-shell;
  }
