{ system ? builtins.currentSystem
, config ? {}
, localPkgs ? import ./. { inherit config system; }
}:
let
  mainShell = localPkgs.nix-tools.libs.cardano-shell.env;
in mainShell // {
  inherit (localPkgs) runCoveralls;
}
