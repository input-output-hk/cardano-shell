let
  commonLib = import ./nix/iohk-common.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, localPkgs ? import ./. { inherit config system; }
, pkgs ? commonLib.getPkgs { inherit config system; }
}:
let
  mainShell = localPkgs.nix-tools.libs.cardano-shell.env;
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
