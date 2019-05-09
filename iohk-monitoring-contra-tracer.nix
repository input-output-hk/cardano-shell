{ mkDerivation, base, contravariant, fetchgit, QuickCheck, random
, stdenv, tasty, tasty-hunit, tasty-quickcheck, text, unix
}:
mkDerivation {
  pname = "contra-tracer";
  version = "0.1.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/iohk-monitoring-framework";
    sha256 = "02yr3alnf74qpa8vg1kk9h034blmb4nzpsbzb0n5jymsyy8r1i4c";
    rev = "d4139f18f77d2f837d52383859a27974f4f4e162";
    fetchSubmodules = true;
  };
  postUnpack = "sourceRoot+=/contra-tracer; echo source root reset to $sourceRoot";
  libraryHaskellDepends = [ base contravariant text unix ];
  testHaskellDepends = [
    base QuickCheck random tasty tasty-hunit tasty-quickcheck text
  ];
  description = "tracing facility";
  license = stdenv.lib.licenses.mit;
}
