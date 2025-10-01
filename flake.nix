{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.05";

    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };

    # Just for a reasonable `haskell-nix`:
    cardano-node = {
      url = "github:IntersectMBO/cardano-node/10.5.1";
      flake = false; # otherwise, +2k dependencies we don’t really use
    };
  };

  outputs = inputs: let
    inherit (inputs.nixpkgs) lib;
  in {
    packages = lib.genAttrs ["x86_64-linux" "x86_64-darwin" "aarch64-darwin"] (system: let
      cardanoNodeFlake = (import inputs.flake-compat { src = inputs.cardano-node; }).defaultNix;
      inherit (cardanoNodeFlake.project.${system}.pkgs) haskell-nix;
      project = haskell-nix.project {
        compiler-nix-name = "ghc96";
        projectFileName = "cabal.project";
        inputMap = { "https://chap.intersectmbo.org/" = cardanoNodeFlake.inputs.CHaP; };
        src = ./.;
      };
    in {
      cardano-launcher = {
        x86_64-linux = project.projectCross.musl64.hsPkgs.cardano-launcher.components.exes.cardano-launcher;
        x86_64-darwin = project.hsPkgs.cardano-launcher.components.exes.cardano-launcher;
        aarch64-darwin = project.hsPkgs.cardano-launcher.components.exes.cardano-launcher;
      }.${system};
    } // lib.optionalAttrs (system == "x86_64-linux") {
      cardano-launcher-x86_64-windows = project.projectCross.mingwW64.hsPkgs.cardano-launcher.components.exes.cardano-launcher;
    });
    hydraJobs = {
      cardano-launcher = {
        x86_64-linux = inputs.self.packages.x86_64-linux.cardano-launcher;
        x86_64-darwin = inputs.self.packages.x86_64-darwin.cardano-launcher;
        aarch64-darwin = inputs.self.packages.aarch64-darwin.cardano-launcher;
        x86_64-windows = inputs.self.packages.x86_64-linux.cardano-launcher-x86_64-windows;
      };
      required = inputs.nixpkgs.legacyPackages.x86_64-linux.releaseTools.aggregate {
        name = "github-required";
        meta.description = "All jobs required to pass CI";
        constituents = __attrValues inputs.self.hydraJobs.cardano-launcher;
      };
    };
  };

  nixConfig = {
    extra-substituters = ["https://cache.iog.io"];
    extra-trusted-public-keys = ["hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="];
    allow-import-from-derivation = "true";
  };
}
