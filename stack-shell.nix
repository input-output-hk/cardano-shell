{ system ? builtins.currentSystem
, config ? {}
}:

let

  nixpkgs = builtins.fetchTarball {
    url    = "https://github.com/NixOS/nixpkgs/archive/6054276a8e6e877f8846c79b0779e3310c495a6b.tar.gz";
    sha256 = "11mv8an4zikh2hybn11znqcbxazqq32byvvvaymy2xkpww2jnkxp";
  };

  pkgs = import nixpkgs { inherit config; };

in
  with pkgs;

  haskell.lib.buildStackProject {
    name = "cardano-shell-env";
    buildInputs = [ zlib openssl git ];
    ghc = haskell.packages.ghc863.ghc;
  }
