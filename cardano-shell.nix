{ mkDerivation, aeson, base, cardano-prelude, dhall, ekg, ekg-core, hspec, katip, QuickCheck
, safe-exceptions, stdenv, text, transformers
}:
mkDerivation {
  pname = "cardano-shell";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base cardano-prelude dhall ekg ekg-core hspec katip QuickCheck safe-exceptions text transformers
  ];
  executableHaskellDepends = [ base cardano-prelude ];
  testHaskellDepends = [ base cardano-prelude ];
  homepage = "https://github.com/input-output-hk/cardano-shell#readme";
  license = stdenv.lib.licenses.mit;
}
