# This will create everything we need to manually test the update system and compress them into
# updater_test.zip.
# Zip file will be located inside result directory.
# How to run: nix-build updater-test-win.nix
let
  commonLib = import ./nix/iohk-common.nix;
  self = import ./. {};
  pkgs = commonLib.getPkgs {};
  crossSelf = import ./. { crossSystem = pkgs.lib.systems.examples.mingwW64; };
  pkgsCross = commonLib.getPkgs { crossSystem = pkgs.lib.systems.examples.mingwW64; };
in pkgs.runCommand "updater_test.zip" { buildInputs = [ pkgs.zip ]; } ''
  mkdir -pv $out/updater-test
  cd $out/updater-test
  mkdir -pv configuration/client configuration/server configuration/launcher
  cp ${crossSelf.nix-tools.cexes.cardano-launcher.cardano-launcher}/bin/cardano-launcher.exe ./cardano-launcher.exe
  cp ${crossSelf.nix-tools.cexes.cardano-launcher.mock-daedalus-frontend}/bin/mock-daedalus-frontend.exe ./daedalus.exe
  cp ${crossSelf.nix-tools.cexes.cardano-launcher.mock-installer}/bin/mock-installer.exe ./updater.exe
  cp ${pkgsCross.libffi}/bin/libffi-6.dll ./
  cp ${./cardano-launcher/configuration/launcher/launcher-config-demo.windows.yaml} ./launcher-config.yaml
  cp ${./cardano-launcher/configuration/cert-configuration.yaml} ./configuration/cert-configuration.yaml
  cp ${./configuration/log-configuration.yaml} ./configuration/log-configuration.yaml
  chmod +w -R .
  cd ..
  zip updater_test.zip -r updater-test/
''

