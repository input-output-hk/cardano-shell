{ system ? builtins.currentSystem
, config ? {}
, pkgs ? import (import ./fetch-nixpkgs.nix) { inherit system config; }
}:

with pkgs;

haskell.lib.buildStackProject {
  name = "cardano-shell";
  buildInputs = [ zlib openssl ];
}
