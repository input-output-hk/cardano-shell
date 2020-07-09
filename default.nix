{ system ? builtins.currentSystem
, crossSystem ? null
# allows to cutomize haskellNix (ghc and profiling, see ./nix/haskell.nix)
, config ? {}
# override scripts with custom configuration
, customConfig ? {}
# allows to override dependencies of the project without modifications,
# eg. to test build against local checkout of nixpkgs and iohk-nix:
# nix build -f default.nix cardano-shell '{
#   iohk-nix = ../iohk-nix;
# }'
, sourcesOverride ? {}
# pinned version of nixpkgs augmented with overlays (iohk-nix and our packages).
, pkgs ? import ./nix { inherit system crossSystem config sourcesOverride; }
, gitrev ? pkgs.iohkNix.commitIdFromGitRepoOrZero ./.git
}:
with pkgs; with commonLib;
let

  haskellPackages = recRecurseIntoAttrs
    # the Haskell.nix package set, reduced to local packages.
    (selectProjectPackages cardanoShellHaskellPackages);

  self = {
    inherit cardanoShellHaskellPackages;
    inherit haskellPackages hydraEvalErrors;

    inherit (haskellPackages.cardano-shell.identifier) version;
    # Grab the executable component of our package.
    inherit (haskellPackages.cardano-shell.components.exes) node-ipc;
    inherit (haskellPackages.cardano-launcher.components.exes) cardano-launcher;

    inherit (pkgs.iohkNix) checkCabalProject;

    # `tests` are the test suites which have been built.
    tests = collectComponents' "tests" haskellPackages;
    # `benchmarks` (only built, not run).
    benchmarks = collectComponents' "benchmarks" haskellPackages;

    checks = recurseIntoAttrs {
      # `checks.tests` collect results of executing the tests:
      tests = collectChecks haskellPackages;
    };

    runCoveralls = cardanoShellHaskellPackages.shellFor {
      name = "run-coveralls";

      packages = ps: with ps; [
         ps.cardano-shell
         ps.cardano-launcher
         ps.cardano-prelude
         ps.canonical-json
         ps.iohk-monitoring
         ps.Win32-network
      ];
  
      # These programs will be available inside the nix-shell.
      buildInputs = (with haskellPackages; [
      ]) ++ (with pkgs; [
        cabal-install
        git
        commonLib.stack-hpc-coveralls
        pkgconfig
      ]);
  
      # Prevents cabal from choosing alternate plans, so that
      # *all* dependencies are provided by Nix.
      exactDeps = true;
  
      GIT_SSL_CAINFO = "${cacert}/etc/ssl/certs/ca-bundle.crt";

      shellHook = ''
        # echo '~~~ cabal coverage'
        # cabal clean
        # cabal build all
      #   cabal test all
      #   echo '~~~ shc'
      #   shc --repo-token=$COVERALLS_REPO_TOKEN combined all
        exit
      '';
    };

    shell = import ./shell.nix {
      inherit pkgs;
      withHoogle = true;
    };
};
in self
