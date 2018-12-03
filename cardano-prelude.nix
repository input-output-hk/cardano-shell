{ mkDerivation, aeson, base, base16-bytestring, bytestring
, canonical-json, cborg, containers, fetchgit, formatting, hashable
, mtl, protolude, stdenv, tagged, text, time
}:
mkDerivation {
  pname = "cardano-prelude";
  version = "0.1.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/cardano-prelude";
    sha256 = "0kimfl3k60jz7cglk24ls5lhvm8xh0hfjs8azhhymzckvyn3y0wn";
    rev = "2d6624af423d0a5c7ced6f3ae465eaaeb4ec739e";
    fetchSubmodules = true;
  };
  libraryHaskellDepends = [
    aeson base base16-bytestring bytestring canonical-json cborg
    containers formatting hashable mtl protolude tagged text time
  ];
  description = "A Prelude replacement for the Cardano project";
  license = stdenv.lib.licenses.mit;
}
