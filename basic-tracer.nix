{ mkDerivation, base, contravariant, QuickCheck, random, stdenv
, tasty, tasty-hunit, tasty-quickcheck, text, unix
}:
mkDerivation {
  pname = "basic-tracer";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base contravariant text unix ];
  testHaskellDepends = [
    base QuickCheck random tasty tasty-hunit tasty-quickcheck text
  ];
  description = "tracing facility";
  license = stdenv.lib.licenses.mit;
}

