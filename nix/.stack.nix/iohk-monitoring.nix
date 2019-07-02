{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {
      disable-aggregation = false;
      disable-ekg = false;
      disable-graylog = false;
      disable-prometheus = false;
      disable-gui = false;
      disable-monitoring = false;
      disable-observables = false;
      disable-syslog = false;
      disable-examples = false;
      queue-flush = false;
      };
    package = {
      specVersion = "1.10";
      identifier = { name = "iohk-monitoring"; version = "0.1.9.0"; };
      license = "MIT";
      copyright = "2018 IOHK";
      maintainer = "";
      author = "Alexander Diemand, Andreas Triantafyllos";
      homepage = "";
      url = "";
      synopsis = "logging, benchmarking and monitoring framework";
      description = "";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = ((((([
          (hsPkgs.base)
          (hsPkgs.contra-tracer)
          (hsPkgs.aeson)
          (hsPkgs.array)
          (hsPkgs.async)
          (hsPkgs.async-timer)
          (hsPkgs.attoparsec)
          (hsPkgs.auto-update)
          (hsPkgs.bytestring)
          (hsPkgs.clock)
          (hsPkgs.containers)
          (hsPkgs.contravariant)
          (hsPkgs.directory)
          (hsPkgs.filepath)
          (hsPkgs.katip)
          (hsPkgs.lens)
          (hsPkgs.mtl)
          (hsPkgs.safe)
          (hsPkgs.safe-exceptions)
          (hsPkgs.scientific)
          (hsPkgs.stm)
          (hsPkgs.template-haskell)
          (hsPkgs.text)
          (hsPkgs.time)
          (hsPkgs.time-units)
          (hsPkgs.transformers)
          (hsPkgs.unordered-containers)
          (hsPkgs.vector)
          (hsPkgs.yaml)
          (hsPkgs.libyaml)
          ] ++ (pkgs.lib).optionals (!flags.disable-ekg) [
          (hsPkgs.ekg)
          (hsPkgs.ekg-core)
          ]) ++ (pkgs.lib).optionals (!flags.disable-ekg && !flags.disable-prometheus) [
          (hsPkgs.ekg-prometheus-adapter)
          (hsPkgs.prometheus)
          (hsPkgs.warp)
          ]) ++ (pkgs.lib).optional (!flags.disable-graylog) (hsPkgs.network)) ++ (pkgs.lib).optional (!flags.disable-gui) (hsPkgs.threepenny-gui)) ++ (if system.isWindows
          then [ (hsPkgs.Win32) ]
          else [
            (hsPkgs.unix)
            ])) ++ (pkgs.lib).optionals (system.isLinux && !flags.disable-syslog) [
          (hsPkgs.hsyslog)
          (hsPkgs.libsystemd-journal)
          ];
        };
      exes = {
        "example-simple" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.iohk-monitoring)
            (hsPkgs.async)
            (hsPkgs.bytestring)
            (hsPkgs.mtl)
            ] ++ (if system.isWindows
            then [ (hsPkgs.Win32) ]
            else [ (hsPkgs.unix) ]);
          };
        "example-complex" = {
          depends = ([
            (hsPkgs.base)
            (hsPkgs.iohk-monitoring)
            (hsPkgs.async)
            (hsPkgs.bytestring)
            (hsPkgs.mtl)
            (hsPkgs.random)
            (hsPkgs.text)
            (hsPkgs.unordered-containers)
            ] ++ (if system.isWindows
            then [ (hsPkgs.Win32) ]
            else [
              (hsPkgs.unix)
              ])) ++ (pkgs.lib).optional (system.isLinux) (hsPkgs.download);
          };
        };
      tests = {
        "tests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.contra-tracer)
            (hsPkgs.iohk-monitoring)
            (hsPkgs.aeson)
            (hsPkgs.array)
            (hsPkgs.async)
            (hsPkgs.bytestring)
            (hsPkgs.clock)
            (hsPkgs.containers)
            (hsPkgs.directory)
            (hsPkgs.filepath)
            (hsPkgs.mtl)
            (hsPkgs.process)
            (hsPkgs.QuickCheck)
            (hsPkgs.random)
            (hsPkgs.semigroups)
            (hsPkgs.split)
            (hsPkgs.stm)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hunit)
            (hsPkgs.tasty-quickcheck)
            (hsPkgs.temporary)
            (hsPkgs.text)
            (hsPkgs.time)
            (hsPkgs.time-units)
            (hsPkgs.transformers)
            (hsPkgs.unordered-containers)
            (hsPkgs.vector)
            (hsPkgs.void)
            (hsPkgs.yaml)
            (hsPkgs.libyaml)
            ];
          };
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/iohk-monitoring-framework";
      rev = "9cb21a3ebf0f45bfb94ece3e6d62e613eca8b17b";
      sha256 = "1nms4gap3j6qc0gs4rk8kpqm6zdqcp5hchsd1wv459wvhfq4f20p";
      });
    postUnpack = "sourceRoot+=/iohk-monitoring; echo source root reset to \$sourceRoot";
    }