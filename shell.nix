let
  localPkgs = import ./. { };
  mainShell = localPkgs.nix-tools.libs.cardano-shell;
in mainShell // {
  inherit (localPkgs) runCoveralls;
}
