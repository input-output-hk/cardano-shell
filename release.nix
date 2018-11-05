with import ./default.nix {};
{ cardano-shell         = cardano-shell.components.exes.cardano-shell-exe;
  cardano-shell-tests   = cardano-shell.components.tests;
  cardano-shell-library = cardano-shell.components.library;
}
