let
  localPkgs = import ./. { };
  mainShell = localPkgs.env;
in mainShell // {
  inherit (localPkgs) runCoveralls;
}
