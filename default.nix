{ config ? {}
, system ? builtins.currentSystem
, iohkLib ? import ./nix/iohk-common.nix { inherit config system; application = "cardano-sl"; }
, pkgs ? iohkLib.pkgs
, gitrev ? iohkLib.commitIdFromGitRepo ./.
}:

import ./nix/pkgs.nix { inherit pkgs; }
