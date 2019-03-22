{ mkDerivation, base, bytestring, conduit, resourcet, stdenv }:
mkDerivation {
  pname = "libyaml";
  version = "0.1.0.0";
  sha256 = "9cd688e316938d8a80536cb1b329c4b651c845e34e045b0c443b345580fb6f07";
  libraryHaskellDepends = [ base bytestring conduit resourcet ];
  homepage = "https://github.com/snoyberg/yaml#readme";
  description = "Low-level, streaming YAML interface";
  license = stdenv.lib.licenses.bsd3;
}
