{ system ? builtins.currentSystem
, config ? {}
, pkgs ? import (import ./scripts/nix/fetch-nixpkgs.nix) { inherit system config; }
}:

with pkgs;

haskell.lib.buildStackProject {
  name = "cardano-shell-env";
  buildInputs = [ zlib openssl git ];
  ghc = haskell.packages.ghc843.ghc;
}
