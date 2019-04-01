{ mkDerivation, base, contravariant, fetchgit, QuickCheck, random
, stdenv, tasty, tasty-hunit, tasty-quickcheck, text, unix
}:
mkDerivation {
  pname = "contra-tracer";
  version = "0.1.0.0";
  src = fetchgit {
    url = "https://github.com/input-output-hk/iohk-monitoring-framework";
    sha256 = "16sxwx8y2wg8kws15ybhk9vkq6crs5bp7ky37x1vrvpvb3ilc5x0";
    rev = "8fb87e83468831289820ef9edb3d5ef912b0db0f";
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
