<<<<<<< HEAD
{ mkDerivation, aeson, base, cardano-prelude, dhall, ekg, ekg-core, katip
, safe-exceptions, stdenv
}:
=======
{ mkDerivation, async, base, cardano-prelude, stdenv, dhall}:
>>>>>>> Remove unused library
mkDerivation {
  pname = "cardano-shell";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
<<<<<<< HEAD
  libraryHaskellDepends = [
    aeson base cardano-prelude dhall ekg ekg-core katip safe-exceptions
  ];
=======
  libraryHaskellDepends = [ async base cardano-prelude dhall];
>>>>>>> Remove unused library
  executableHaskellDepends = [ base cardano-prelude ];
  testHaskellDepends = [ base cardano-prelude ];
  homepage = "https://github.com/input-output-hk/cardano-shell#readme";
  license = stdenv.lib.licenses.mit;
}
