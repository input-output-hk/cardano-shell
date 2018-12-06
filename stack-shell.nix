{ system ? builtins.currentSystem
, config ? {}
}:

let

  nixpkgs = builtins.fetchTarball {
    url    = "https://github.com/NixOS/nixpkgs/archive/069bf7aee30faf7b3ed773cfae2154d761b2d6c2.tar.gz";
    sha256 = "1c44vjb60fw2r8ck8yqwkj1w4288wixi59c6w1vazjixa79mvjvg";
  };

  pkgs = import nixpkgs { inherit config; };

in
  with pkgs;

  haskell.lib.buildStackProject {
    name = "cardano-shell-env";
    buildInputs = [ zlib openssl git ];
    ghc = haskell.packages.ghc844.ghc;
  }
