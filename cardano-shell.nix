{ mkDerivation, aeson, async, base, binary, bytestring, Cabal
, cardano-prelude, cardano-sl-x509, concurrency, containers
, contravariant, dejafu, dhall, directory, filepath
, formatting, hspec, hspec-contrib, hunit-dejafu, iohk-monitoring
, process, QuickCheck, safe-exceptions, stdenv, stm, text, transformers
, turtle, unix
}:
mkDerivation {
  pname = "cardano-shell";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base binary bytestring Cabal cardano-prelude concurrency
    containers contravariant dhall directory formatting
    iohk-monitoring process QuickCheck safe-exceptions stm text
    transformers unix
  ];
  executableHaskellDepends = [
    async base cardano-prelude cardano-sl-x509 directory filepath
    formatting iohk-monitoring process safe-exceptions turtle unix
  ];
  testHaskellDepends = [
    aeson base cardano-prelude concurrency dejafu dhall hspec
    hspec-contrib hunit-dejafu QuickCheck safe-exceptions
  ];
  homepage = "https://github.com/input-output-hk/cardano-shell#readme";
  license = stdenv.lib.licenses.mit;
}
