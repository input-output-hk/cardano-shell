{ mkDerivation, aeson, array, async, async-timer, attoparsec
, auto-update, base, basic-tracer, bytestring, clock, containers
, contravariant, directory, download, ekg, ekg-core, fetchgit
, filepath, katip, lens, libyaml, mtl, process, QuickCheck, random
, safe, safe-exceptions, scientific, semigroups, split, stdenv, stm
, tasty, tasty-hunit, tasty-quickcheck, template-haskell, text
, threepenny-gui, time, time-units, transformers, unix
, unordered-containers, vector, void, yaml
}:
mkDerivation {
  pname = "iohk-monitoring";
  version = "0.1.3.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/iohk-monitoring-framework";
    sha256 = "1kvsx5bz9hnkwipz9zphcnangqbmqzj266xkb0kxc61sdf2yqhv5";
    rev = "cdbcf35ad7a3b8f90c95f0dc42f7fb111d2d689c";
    fetchSubmodules = true;
  };
  postUnpack = "sourceRoot+=/iohk-monitoring; echo source root reset to $sourceRoot";
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson array async async-timer attoparsec auto-update base
    basic-tracer bytestring clock containers contravariant directory
    ekg ekg-core filepath katip lens libyaml mtl safe safe-exceptions
    scientific stm template-haskell text threepenny-gui time time-units
    transformers unix unordered-containers vector yaml
  ];
  executableHaskellDepends = [
    async base bytestring download mtl random text unix
  ];
  testHaskellDepends = [
    aeson array async base basic-tracer bytestring clock containers
    directory filepath libyaml mtl process QuickCheck random semigroups
    split stm tasty tasty-hunit tasty-quickcheck text time time-units
    transformers unordered-containers vector void yaml
  ];
  description = "logging, benchmarking and monitoring framework";
  license = stdenv.lib.licenses.mit;
}
