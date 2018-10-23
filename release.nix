let

  config = {
    packageOverrides = pkgs: rec {
      haskellPackages = pkgs.haskell.packages.ghc822.override {
        overrides = haskellPackagesNew: haskellPackagesOld: rec {
          universum           = pkgs.haskell.lib.dontCheck (haskellPackagesNew.callHackage "universum" "1.1.0" {});
          # LIB
          cardano-shell  = haskellPackagesNew.callPackage ./cardano-shell.nix { }; 
          cardano-chain-env = pkgs.haskell.lib.dontCheck (haskellPackagesNew.lib.buildStackProject { 
                                                            name = "cardano-chain-env";
                                                            buildInputs = with pkgs; [ zlib openssl ];
                                                            });
        };
      };
    };
  };

  # pinning
  fetchNixPkgs  = import ./scripts/nix/fetchNixpkgs.nix (builtins.fromJSON (builtins.readFile ./scripts/nix/nixpkgs-src.json));
  pkgs          = import fetchNixPkgs { inherit config; };

in
  { cardano-shell = pkgs.haskellPackages.cardano-shell;
  }
