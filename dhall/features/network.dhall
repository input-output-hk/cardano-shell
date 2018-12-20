\(cluster : ../types/cluster.type) ->
\(os: ../types/os.type) ->
\(launcher : ../types/launcher.type) ->
\(topology : ../types/topology.type) ->
{ configurationYaml = os.osConfigurationYaml
, topology          = os.osNodeArgs.naTopology
, x509ToolPath      = os.osX509ToolPath
, tlsPath           = os.osNodeArgs.naTlsPath
, walletPort        = cluster.ccfgWalletPort
, host              = cluster.ccfgRelays
, valency           = topology.wallet.wcfgValency
, fallback          = topology.wallet.wcfgFallbacks
, tlsca             = launcher.lTlsca
, tlscert           = launcher.lTlscert
, tlsKey            = launcher.lTlsKey
}