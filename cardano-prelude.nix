{ mkDerivation, aeson, base, base16-bytestring, bytestring
, canonical-json, cborg, containers, fetchgit, formatting, hashable
, mtl, protolude, stdenv, tagged, text, time
}:
mkDerivation {
  pname = "cardano-prelude";
  version = "0.1.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/cardano-prelude";
    sha256 = "1vlqhv7iqrjdaa8yd04k34xwqp13mz2nhz4mj923qmrjf9p55sfz";
    rev = "0a32ec92c461e144f981864c97546db11b52e46a";
    fetchSubmodules = true;
  };
  libraryHaskellDepends = [
    aeson base base16-bytestring bytestring canonical-json cborg
    containers formatting hashable mtl protolude tagged text time
  ];
  description = "A Prelude replacement for the Cardano project";
  license = stdenv.lib.licenses.mit;
}
