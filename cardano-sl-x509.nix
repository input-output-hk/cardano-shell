{ mkDerivation, aeson, asn1-encoding, asn1-types, base
, base64-bytestring, bytestring, cryptonite, data-default-class
, directory, fetchgit, filepath, hedgehog, hourglass, ip
, QuickCheck, stdenv, universum, unordered-containers, x509
, x509-store, x509-validation, yaml
}:
mkDerivation {
  pname = "cardano-sl-x509";
  version = "3.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/cardano-sl-x509";
    sha256 = "16npjbnwiwvslc6fxamg84q31f0wsl01g9yr3nkmymvnk4lff2g3";
    rev = "71115d199368f1cc969a4936a856808539063253";
    fetchSubmodules = true;
  };
  libraryHaskellDepends = [
    aeson asn1-encoding asn1-types base base64-bytestring bytestring
    cryptonite data-default-class directory filepath hourglass ip
    universum unordered-containers x509 x509-store x509-validation yaml
  ];
  testHaskellDepends = [ base hedgehog QuickCheck universum ];
  homepage = "https://github.com/input-output-hk/cardano-sl/x509/README.md";
  description = "Tool-suite for generating x509 certificates specialized for RSA with SHA-256";
  license = stdenv.lib.licenses.mit;
}
