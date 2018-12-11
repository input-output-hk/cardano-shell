{ mkDerivation, aeson, base, cardano-prelude, concurrency, dejafu
, directory, ekg, ekg-core, formatting, hspec, hspec-contrib
, hunit-dejafu, katip, QuickCheck, safe-exceptions, stdenv
}:
mkDerivation {
  pname = "cardano-shell";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base cardano-prelude concurrency directory ekg ekg-core
    formatting katip safe-exceptions
  ];
  executableHaskellDepends = [ base cardano-prelude ];
  testHaskellDepends = [
    base cardano-prelude concurrency dejafu hspec hspec-contrib
    hunit-dejafu QuickCheck
  ];
  homepage = "https://github.com/input-output-hk/cardano-shell#readme";
  license = stdenv.lib.licenses.mit;
}
