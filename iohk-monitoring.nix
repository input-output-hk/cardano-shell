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
    sha256 = "19v6nbgc89hjj052qklj3pqigb3n8innmghka03jm6cc52q9j41h";
    rev = "7a507a9d7b53686886a725c57494e2165043a75a";
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
