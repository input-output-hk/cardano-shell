{
  extras = hackage:
    {
      packages = {
        "katip" = (((hackage.katip)."0.8.3.0").revisions).default;
        "quickcheck-state-machine" = (((hackage.quickcheck-state-machine)."0.6.0").revisions).default;
        "pretty-show" = (((hackage.pretty-show)."1.9.5").revisions).default;
        "time-units" = (((hackage.time-units)."1.0.0").revisions).default;
        "silently" = (((hackage.silently)."1.2.5.1").revisions).default;
        "base58-bytestring" = (((hackage.base58-bytestring)."0.1.0").revisions).default;
        "hedgehog" = (((hackage.hedgehog)."1.0").revisions).default;
        "micro-recursion-schemes" = (((hackage.micro-recursion-schemes)."5.0.2.2").revisions).default;
        "streaming-binary" = (((hackage.streaming-binary)."0.3.0.1").revisions).default;
        "cborg" = (((hackage.cborg)."0.2.2.0").revisions).default;
        "canonical-json" = (((hackage.canonical-json)."0.6.0.0").revisions).default;
        "Win32" = (((hackage.Win32)."2.5.4.1").revisions)."e623a1058bd8134ec14d62759f76cac52eee3576711cb2c4981f398f1ec44b85";
        } // {
        cardano-shell = ./cardano-shell.nix;
        cardano-launcher = ./cardano-launcher.nix;
        cardano-prelude = ./cardano-prelude.nix;
        cardano-prelude-test = ./cardano-prelude-test.nix;
        contra-tracer = ./contra-tracer.nix;
        iohk-monitoring = ./iohk-monitoring.nix;
        cardano-sl-x509 = ./cardano-sl-x509.nix;
        cardano-crypto = ./cardano-crypto.nix;
        };
      compiler.version = "8.10.6";
      compiler.nix-name = "ghc810";
      };
  resolver = "lts-13.26";
  compiler = "ghc-8.10.6";
  }