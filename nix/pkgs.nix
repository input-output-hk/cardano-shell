# our packages overlay
pkgs: _: with pkgs; {
  cardanoShellHaskellPackages = import ./haskell.nix {
    inherit config
      lib
      stdenv
      haskell-nix
      buildPackages
      ;
  };
}
