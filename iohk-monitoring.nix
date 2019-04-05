{ mkDerivation, aeson, array, async, async-timer, attoparsec
, auto-update, base, contra-tracer, bytestring, clock, containers
, contravariant, directory, download, ekg, ekg-core, fetchgit
, filepath, katip, lens, libyaml, mtl, process, QuickCheck, random
, safe, safe-exceptions, scientific, semigroups, split, stdenv, stm
, tasty, tasty-hunit, tasty-quickcheck, template-haskell, text
, threepenny-gui, time, time-units, transformers, unix
, unordered-containers, vector, void, yaml
}:
mkDerivation {
  pname = "iohk-monitoring";
  version = "0.1.5.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/iohk-monitoring-framework";
    sha256 = "16sxwx8y2wg8kws15ybhk9vkq6crs5bp7ky37x1vrvpvb3ilc5x0";
    rev = "8fb87e83468831289820ef9edb3d5ef912b0db0f";
    fetchSubmodules = true;
  };
  postUnpack = "sourceRoot+=/iohk-monitoring; echo source root reset to $sourceRoot";
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson array async async-timer attoparsec auto-update base
    contra-tracer bytestring clock containers contravariant directory
    ekg ekg-core filepath katip lens libyaml mtl safe safe-exceptions
    scientific stm template-haskell text threepenny-gui time time-units
    transformers unix unordered-containers vector yaml
  ];
  executableHaskellDepends = [
    async base bytestring download mtl random text unix
  ];
  testHaskellDepends = [
    aeson array async base contra-tracer bytestring clock containers
    directory filepath libyaml mtl process QuickCheck random semigroups
    split stm tasty tasty-hunit tasty-quickcheck text time time-units
    transformers unordered-containers vector void yaml
  ];
  description = "logging, benchmarking and monitoring framework";
  license = stdenv.lib.licenses.mit;
}
