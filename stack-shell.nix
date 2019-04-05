{ system ? builtins.currentSystem
, config ? {}
}:
(import ./default.nix { inherit system config; }).stack-env
