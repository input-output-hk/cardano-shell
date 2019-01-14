let
  config = import ./config.nix;
  nixpkgs = import ./nixpkgs.nix;
  pkgs = import nixpkgs { inherit config; };
in {
  cardano-shell = pkgs.haskellPackages.cardano-shell;
}
