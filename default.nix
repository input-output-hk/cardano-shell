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
    (selectProjectPackages cardanoNodeHaskellPackages);

  # stack needs to be version 1.9.3, because versions greater than two can't be
  # re-execed in a nix shell:
  #
  #https://github.com/commercialhaskell/stack/issues/5000
  nixpkgs-19-03-tarball = builtins.fetchTarball {
    # Channel nixos-19.03 as of 2019/08/12.
    url = "https://github.com/NixOS/nixpkgs/archive/56d94c8c69f8cac518027d191e2f8de678b56088.tar.gz";
    sha256 = "1c812ssgmnmh97sarmp8jcykk0g57m8rsbfjg9ql9996ig6crsmi";
  };

  nixpkgs-19-03 = import nixpkgs-19-03-tarball {};

  stack_1_9_3 = nixpkgs-19-03.stack;

  self = {
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

    runCoveralls = pkgs.stdenv.mkDerivation {
      name = "run-coveralls";
      buildInputs = with pkgs; [ commonLib.stack-hpc-coveralls stack_1_9_3 git ];
      shellHook = ''
        echo '~~~ stack nix test'
        stack test --nix --coverage
        echo '~~~ shc'
        shc --repo-token=$COVERALLS_REPO_TOKEN combined all
        exit
      '';
      STACK_IN_NIX_SHELL = true;
    };

    shell = import ./shell.nix {
      inherit pkgs;
      withHoogle = true;
    };
};
in self
