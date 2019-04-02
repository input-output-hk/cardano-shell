{ iohkLib ? import ../../nix/iohk-common.nix { application = "cardano-sl"; }
, pkgs ? iohkLib.pkgs
, buildTools ? with pkgs; [ git nix gnumake ]
}:

with pkgs.lib;
with pkgs;

let
  cache-s3 = callPackage ./cache-s3.nix {};

  stackRebuild = runCommand "stack-rebuild" {} ''
    ${haskellPackages.ghcWithPackages (ps: [ps.turtle ps.safe ps.transformers])}/bin/ghc -o $out ${./rebuild.hs}
  '';

in
  writeScript "stack-rebuild-wrapped" ''
    #!${stdenv.shell}
    export PATH=${lib.makeBinPath ([ cache-s3 stack gnused coreutils ] ++ buildTools)}
    exec ${stackRebuild} "$@"
  ''
