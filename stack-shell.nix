{ config ? {}
, system ? builtins.currentSystem
}:

let

  iohkLib = import ./nix/iohk-common.nix { inherit config system; application = "cardano-sl"; };

in
  with iohkLib.pkgs;

  haskell.lib.buildStackProject {
    name = "cardano-shell-env";
    buildInputs = [ zlib openssl git ];
    ghc = haskell.packages.ghc862.ghc;
  }
