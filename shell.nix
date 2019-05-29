{ system ? builtins.currentSystem
, config ? {}
, localPkgs ? import ./. { inherit config system; }
}:
let
  localPkgs = import ./. { };
  mainShell = localPkgs.nix-tools.libs.cardano-shell;
in mainShell // {
  inherit (localPkgs) runCoveralls;
}
