{ mkDerivation, aeson, Cabal, array, async, auto-update, base, bytestring
, clock, containers, contravariant, directory, ekg, ekg-core, fetchgit
, filepath, katip, lens, mtl, process, QuickCheck, random
, safe-exceptions, semigroups, stdenv, stm, tasty, tasty-hunit
, tasty-quickcheck, template-haskell, text, time, time-units
, transformers, unix, unordered-containers, void, yaml
}:
mkDerivation {
  pname = "iohk-monitoring";
  version = "0.1.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/iohk-monitoring-framework";
    sha256 = "1qk5zin92bfn635nyi31b8w2nrw8zdcc8p0x2s2xcq9mzc3zdybf";
    rev = "4dc4d541a645b84a281faa8950a7fd4e61708963";
    fetchSubmodules = false;
  };
  libraryHaskellDepends = [
    aeson Cabal array async auto-update base bytestring clock containers
    contravariant directory ekg ekg-core filepath katip lens mtl
    safe-exceptions stm template-haskell text time time-units
    transformers unix unordered-containers yaml
  ];
  testHaskellDepends = [
    Cabal array base bytestring clock containers mtl process QuickCheck
    random semigroups stm tasty tasty-hunit tasty-quickcheck text time
    time-units transformers void
  ];
  description = "logging, benchmarking and monitoring framework";
  license = stdenv.lib.licenses.mit;
  hydraPlatforms = stdenv.lib.platforms.none;
}
