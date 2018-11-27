{ mkDerivation, aeson, base, cardano-prelude, dhall, ekg, ekg-core, katip
, safe-exceptions, stdenv
}:
mkDerivation {
  pname = "cardano-shell";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base cardano-prelude dhall ekg ekg-core katip safe-exceptions
  ];
  executableHaskellDepends = [ base cardano-prelude ];
  testHaskellDepends = [ base cardano-prelude ];
  homepage = "https://github.com/input-output-hk/cardano-shell#readme";
  license = stdenv.lib.licenses.mit;
}
