{ mkDerivation, base, bytestring, containers, fetchgit, parsec
, pretty, stdenv
}:
mkDerivation {
  pname = "canonical-json";
  version = "0.5.0.1";
  src = fetchgit {
    url = "https://github.com/well-typed/canonical-json";
    sha256 = "0bmh3q9m74r6j4zbr9aph44j6h6snlqvargfi8vz7228gknhldhd";
    rev = "0d2426c6e2bf87388fb4ded751c514d2a2d560b2";
    fetchSubmodules = true;
  };
  libraryHaskellDepends = [
    base bytestring containers parsec pretty
  ];
  description = "Canonical JSON for signing and hashing JSON values";
  license = stdenv.lib.licenses.bsd3;
}
