{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "cardano-prelude"; version = "0.1.0.0"; };
      license = "MIT";
      copyright = "2018 IOHK";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "";
      url = "";
      synopsis = "A Prelude replacement for the Cardano project";
      description = "A Prelude replacement for the Cardano project";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.aeson)
          (hsPkgs.array)
          (hsPkgs.base16-bytestring)
          (hsPkgs.bytestring)
          (hsPkgs.canonical-json)
          (hsPkgs.cborg)
          (hsPkgs.containers)
          (hsPkgs.formatting)
          (hsPkgs.ghc-prim)
          (hsPkgs.hashable)
          (hsPkgs.integer-gmp)
          (hsPkgs.mtl)
          (hsPkgs.nonempty-containers)
          (hsPkgs.protolude)
          (hsPkgs.tagged)
          (hsPkgs.text)
          (hsPkgs.time)
          (hsPkgs.vector)
          ];
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/cardano-prelude";
      rev = "2256fd727c5f92e6218afdcf8cddf6e01c4a9dcd";
      sha256 = "0fdwlhkpc7inkqflcdzinx9qr5g3i34clzhl6iiagj851c3jcgsn";
      });
    }