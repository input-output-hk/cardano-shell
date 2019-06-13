let
  shell = import ./. {};
  pkgs = shell._lib.pkgs;
  # partial code for testing on a cross arch
  cross-ipc = (import ./release.nix {}).nix-tools.cexes.x86_64-pc-mingw32-cardano-shell.node-ipc.x86_64-linux;
  crossShell = pkgs.mkShell {
    name = "test";
    buildInputs = [ cross-ipc pkgs.wineWowPackages.minimal ];
  };
  # test the ipc on a given native arch
  mkTest = arch: {
    name = arch;
    value = let
      pkgs = shell._lib.getPkgs { system = arch; };
      shell = import ./. { system = arch; };
    in pkgs.runCommand "test-ipc-${arch}" {
      buildInputs = [ shell.nix-tools.cexes.cardano-shell.node-ipc pkgs.nodejs ];
    } ''
      cp ${./app/NodeIPCClient/server.js} server.js
      node server.js
      touch $out
    '';
  };
in builtins.listToAttrs (map mkTest [ "x86_64-linux" "x86_64-darwin" ])
