{ mkDerivation, base, contravariant, fetchgit, QuickCheck, random
, stdenv, tasty, tasty-hunit, tasty-quickcheck, text, unix
}:
mkDerivation {
  pname = "basic-tracer";
  version = "0.1.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/iohk-monitoring-framework";
    sha256 = "1kvsx5bz9hnkwipz9zphcnangqbmqzj266xkb0kxc61sdf2yqhv5";
    rev = "cdbcf35ad7a3b8f90c95f0dc42f7fb111d2d689c";
    fetchSubmodules = true;
  };
  postUnpack = "sourceRoot+=/basic-tracer; echo source root reset to $sourceRoot";
  libraryHaskellDepends = [ base contravariant text unix ];
  testHaskellDepends = [
    base QuickCheck random tasty tasty-hunit tasty-quickcheck text
  ];
  description = "tracing facility";
  license = stdenv.lib.licenses.mit;
}
