{ mkDerivation, aeson, base, bytestring, containers, deepseq
, directory, docopt, fetchgit, filepath, hlint, hpc, hspec
, hspec-contrib, http-client, HUnit, lens, lens-aeson, process
, pureMD5, stdenv, text, time, unordered-containers, utf8-string
, wreq, yaml
}:
mkDerivation {
  pname = "stack-hpc-coveralls";
  version = "0.0.4.0";
  src = fetchgit {
    url = "https://github.com/rubik/stack-hpc-coveralls";
    sha256 = "1k1rbndfb4shaknc368yyf9p680kfr9b9di5w6yfw9y5a1cschhc";
    rev = "3d8352d5642ab214a7a574bd797880ae39595a44";
    fetchSubmodules = true;
  };
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base bytestring containers directory filepath hpc http-client
    lens lens-aeson process pureMD5 text unordered-containers
    utf8-string wreq yaml
  ];
  executableHaskellDepends = [ aeson base bytestring docopt ];
  testHaskellDepends = [
    aeson base containers deepseq hlint hpc hspec hspec-contrib HUnit
    time
  ];
  homepage = "http://github.com/rubik/stack-hpc-coveralls";
  description = "Initial project template from stack";
  license = stdenv.lib.licenses.isc;
}
