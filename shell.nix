{ system ? builtins.currentSystem
, config ? {}
, localPkgs ? import ./. { inherit config system; }
}:
let
  # mainShell = localPkgs.nix-tools.libs.cardano-shell.env;
  mainShell = localPkgs.nix-tools.libs.cardano-shell;
in mainShell // {
  inherit (localPkgs) runCoveralls;
}
