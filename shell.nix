let
  hsPkgs = import ./default.nix {};
  mainShell = hsPkgs.haskellPackages.cardano-shell.components.all;
  pkgs = import (import ./nixpkgs.nix) { config = import ./config.nix; };
  runCoveralls = pkgs.stdenv.mkDerivation {
    name = "run-coveralls";
    buildInputs = [ pkgs.haskellPackages.stack-hpc-coveralls pkgs.stack ];
    shellHook = ''
      echo '~~~ stack test'
      stack test --coverage
      echo '~~~ shc'
      shc --repo-token=$COVERALLS_REPO_TOKEN cardano-shell cardano-shell-test
      exit
    '';
  };
in mainShell // {
  inherit runCoveralls;
}
