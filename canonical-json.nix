{ mkDerivation, base, bytestring, containers, fetchgit, parsec
, pretty, stdenv
}:
mkDerivation {
  pname = "canonical-json";
  version = "0.5.0.0";
  src = fetchgit {
    url = "https://github.com/well-typed/canonical-json";
    sha256 = "19lc5pr85jz3f8ifmjxnkxgib0lz3vgagdny50gb04midc7y37pr";
    rev = "2d261bb971bada1893753b503452d9e6e217bc4a";
    fetchSubmodules = true;
  };
  libraryHaskellDepends = [
    base bytestring containers parsec pretty
  ];
  description = "Canonical JSON for signing and hashing JSON values";
  license = stdenv.lib.licenses.bsd3;
}
