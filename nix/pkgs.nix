{ args ? { config = import ./config.nix; }
, pkgs ? import <nixpkgs> { inherit args; }
, src ? ../.
}:
let
  overrideWith = override: default:
   let
     try = builtins.tryEval (builtins.findFile builtins.nixPath override);
   in if try.success then
     builtins.trace "using search host <${override}>" try.value
   else
     default;
in
let
  # all packages from hackage as nix expressions
  hackage = import (overrideWith "hackage"
                    (pkgs.fetchFromGitHub { owner  = "input-output-hk";
                                            repo   = "hackage.nix";
                                            rev    = "5223a45e08b1b0d738fdd292b39e49f39f21536f";
                                            sha256 = "09r662kn2qs444fmqni9jamaxnrk9jrg6whqmxbwhfgd5vy3yynq";
                                            name   = "hackage-exprs-source"; }))
                   ;
  # a different haskell infrastructure
  haskell = import (overrideWith "haskell"
                    (pkgs.fetchFromGitHub { owner  = "input-output-hk";
                                            repo   = "haskell.nix";
                                            rev    = "34511726b7b43a8a22f8026b4e9f9672e57b2cd6";
                                            sha256 = "01zm6337b1zcc42s22bpb21xhmhhhgnv0ds3r0p8mc1sb62l0zwg";
                                            name   = "haskell-lib-source"; }))
                   hackage;

  # the set of all stackage snapshots
  stackage = import (overrideWith "stackage"
                     (pkgs.fetchFromGitHub { owner  = "input-output-hk";
                                             repo   = "stackage.nix";
                                             rev    = "ee2b3a71ce8eca1a40eee8a928644dd9912218fe";
                                             sha256 = "1463d8b3cfsw0xwl9ln8kylm98bp4c518kql4ydw2ggdvihyh20v";
                                             name   = "stackage-snapshot-source"; }))
                   ;

  # our packages
  stack-pkgs = import ./.stack-pkgs.nix;

  # The compiler referenced in the stack config
  compiler = (stack-pkgs.overlay hackage).compiler.nix-name;

  # Build the packageset with module support.
  # We can essentially override anything in the modules
  # section.
  #
  #  packages.cbors.patches = [ ./one.patch ];
  #  packages.cbors.flags.optimize-gmp = false;
  #
  pkgSet = haskell.mkPkgSet {
    inherit pkgs;
    pkg-def = stackage.${stack-pkgs.resolver};
    pkg-def-overlays = [
      stack-pkgs.overlay
    ];
    modules = [
      haskell.ghcHackagePatches.${compiler}

      { packages.cardano-wallet.src = pkgs.lib.mkForce src; }
    ];
  };

  packages = pkgSet.config.hsPkgs // { _config = pkgSet.config; };

in packages
