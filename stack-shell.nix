{ system ? builtins.currentSystem
, config ? {}
, localPkgs ? import ./. { inherit config system; }
, pkgs ? localPkgs._lib.getPkgs { inherit config system; }
}:
with pkgs; haskell.lib.buildStackProject {
  name = "cardano-shell-env";
  buildInputs = [ zlib openssl git ];
  ghc = haskell.packages.ghc863.ghc;
}
