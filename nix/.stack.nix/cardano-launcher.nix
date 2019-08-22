{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.2";
      identifier = { name = "cardano-launcher"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2018 IOHK";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "https://github.com/input-output-hk/cardano-shell#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/githubuser/cardano-shell#readme>";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.Cabal)
          (hsPkgs.cardano-prelude)
          (hsPkgs.containers)
          (hsPkgs.directory)
          (hsPkgs.process)
          (hsPkgs.QuickCheck)
          (hsPkgs.text)
          (hsPkgs.turtle)
          ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs.Win32);
        };
      exes = {
        "cardano-launcher" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.cardano-prelude)
            (hsPkgs.cardano-launcher)
            (hsPkgs.cardano-sl-x509)
            (hsPkgs.directory)
            (hsPkgs.filepath)
            (hsPkgs.formatting)
            (hsPkgs.safe-exceptions)
            ];
          };
        };
      tests = {
        "cardano-launcher-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.cardano-launcher)
            (hsPkgs.cardano-prelude)
            (hsPkgs.QuickCheck)
            (hsPkgs.hspec)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../../././cardano-launcher; }