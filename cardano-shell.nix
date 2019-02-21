{ mkDerivation, base, cardano-prelude, concurrency, contravariant
, dejafu, dhall, directory, ekg-core, formatting, hspec
, hspec-contrib, hunit-dejafu, iohk-monitoring, QuickCheck
, safe-exceptions, stdenv, text, transformers
}:
mkDerivation {
  pname = "cardano-shell";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base cardano-prelude concurrency contravariant dhall directory
    ekg-core formatting QuickCheck safe-exceptions text transformers
  ];
  executableHaskellDepends = [
    base cardano-prelude iohk-monitoring safe-exceptions
  ];
  testHaskellDepends = [
    base cardano-prelude concurrency dejafu dhall hspec hspec-contrib
    hunit-dejafu QuickCheck safe-exceptions
  ];
  homepage = "https://github.com/input-output-hk/cardano-shell#readme";
  license = stdenv.lib.licenses.mit;
}
