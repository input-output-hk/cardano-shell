{
  extras = hackage:
    {
      packages = {
        "base58-bytestring" = (((hackage.base58-bytestring)."0.1.0").revisions).default;
        "half" = (((hackage.half)."0.2.2.3").revisions).default;
        "micro-recursion-schemes" = (((hackage.micro-recursion-schemes)."5.0.2.2").revisions).default;
        "streaming-binary" = (((hackage.streaming-binary)."0.3.0.1").revisions).default;
        "pretty-show" = (((hackage.pretty-show)."1.8.2").revisions).default;
        "katip" = (((hackage.katip)."0.7.0.0").revisions)."4b30d0643e18d01a3fd264d3d75921b49b2f464336a52fa46fa049107ebbfe04";
        "time-units" = (((hackage.time-units)."1.0.0").revisions)."27cf54091c4a0ca73d504fc11d5c31ab4041d17404fe3499945e2055697746c1";
        "ekg" = (((hackage.ekg)."0.4.0.15").revisions)."f52d7c00654d72d2ab988255f30adba95a52484ac310bab9c136c64732e69f4b";
        "ekg-json" = (((hackage.ekg-json)."0.1.0.6").revisions)."4ff2e9cac213a5868ae8b4a7c72a16a9a76fac14d944ae819b3d838a9725569b";
        } // {
        cardano-shell = ./cardano-shell.nix;
        cardano-prelude = ./cardano-prelude.nix;
        cardano-prelude-test = ./cardano-prelude-test.nix;
        contra-tracer = ./contra-tracer.nix;
        iohk-monitoring = ./iohk-monitoring.nix;
        cardano-sl-x509 = ./cardano-sl-x509.nix;
        cborg = ./cborg.nix;
        cardano-crypto = ./cardano-crypto.nix;
        plutus-prototype = ./plutus-prototype.nix;
        hedgehog = ./hedgehog.nix;
        canonical-json = ./canonical-json.nix;
        };
      compiler.version = "8.6.3";
      compiler.nix-name = "ghc863";
      };
  resolver = "lts-13.4";
  compiler = "ghc-8.6.3";
  }