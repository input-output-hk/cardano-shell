{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "cardano-prelude-test"; version = "0.1.0.0"; };
      license = "MIT";
      copyright = "2018 IOHK";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "";
      url = "";
      synopsis = "Utility types and functions for testing Cardano";
      description = "Utility types and functions for testing Cardano";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.aeson)
          (hsPkgs.aeson-pretty)
          (hsPkgs.attoparsec)
          (hsPkgs.base16-bytestring)
          (hsPkgs.bytestring)
          (hsPkgs.canonical-json)
          (hsPkgs.cardano-prelude)
<<<<<<< HEAD
          (hsPkgs.containers)
=======
>>>>>>> Update build to use nix-tools.
          (hsPkgs.cryptonite)
          (hsPkgs.formatting)
          (hsPkgs.hedgehog)
          (hsPkgs.hspec)
          (hsPkgs.pretty-show)
          (hsPkgs.QuickCheck)
          (hsPkgs.quickcheck-instances)
          (hsPkgs.text)
<<<<<<< HEAD
          (hsPkgs.template-haskell)
=======
>>>>>>> Update build to use nix-tools.
          (hsPkgs.time)
          ];
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/cardano-prelude";
<<<<<<< HEAD
      rev = "892661cc3951e0d3a385c49c4563b2ae1cf9a4c2";
      sha256 = "0nnplb68q18bcbgl49dh0m3lppm7v5ys1svk9q3kpl0yihydh9s5";
=======
      rev = "2256fd727c5f92e6218afdcf8cddf6e01c4a9dcd";
      sha256 = "0fdwlhkpc7inkqflcdzinx9qr5g3i34clzhl6iiagj851c3jcgsn";
>>>>>>> Update build to use nix-tools.
      });
    postUnpack = "sourceRoot+=/test; echo source root reset to \$sourceRoot";
    }