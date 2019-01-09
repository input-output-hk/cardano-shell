\(cluster : ../types/cluster.type) ->
\(os: ../types/os.type) ->
\(launcher : ../types/launcher.type) ->
\(topology : ../types/topology.type) ->
{ networkConfigurationYaml = os.osConfigurationYaml
, networkTopology          = os.osNodeArgs.naTopology
, networkX509ToolPath      = os.osX509ToolPath
, networkTlsPath           = os.osNodeArgs.naTlsPath
, networkHost              = cluster.ccfgRelays
, networkValency           = topology.wallet.wcfgValency
, networkFallback          = topology.wallet.wcfgFallbacks
, networkTlsca             = launcher.lTlsca
, networkTlscert           = launcher.lTlscert
, networkTlskey            = launcher.lTlsKey
}