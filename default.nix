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

  # FIXME: I really don’t know if this ↓ is right… – @michalrus
  hpc-coveralls = cardanoShellHaskellPackages.tool "hpc-coveralls" "0.7.0";

  haskellPackages = recRecurseIntoAttrs
    # the Haskell.nix package set, reduced to local packages.
    (selectProjectPackages cardanoShellHaskellPackages);

  uploadCoverallsScript = pkgSet:
    let
      projectPkgs = selectProjectPackages pkgSet;
      projectCoverageReport = pkgSet.projectCoverageReport;
    in writeShellScriptBin "uploadCoveralls.sh" ''
      ${hpc-coveralls}/bin/hpc-coveralls all \
        ${concatStringsSep "\n  " (mapAttrsToList (_: p: "--package-dir .${p.src.origSubDir} \\") projectPkgs)}
        --hpc-dir ${projectCoverageReport}/share/hpc/vanilla \
        --coverage-mode StrictlyFullLines \
        --repo-token=$COVERALLS_REPO_TOKEN
    '';

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

    inherit hpc-coveralls;
    uploadCoverallsScript = uploadCoverallsScript cardanoShellHaskellPackages;

    shell = import ./shell.nix {
      inherit pkgs;
      withHoogle = true;
    };
  };
in self
