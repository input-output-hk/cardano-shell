\(cluster : ../types/cluster.type) ->
\(os: ../types/os.type) ->
\(launcher : ../types/launcher.type) ->
\(topology : ../types/topology.type) ->
{ networkConfigurationYaml = {getConfigurationYamlPath = os.osConfigurationYaml}
, networkTopology          = {getTopology = os.osNodeArgs.naTopology}
, networkX509ToolPath      = {getX509ToolPath = os.osX509ToolPath}
, networkTlsPath           = {getTlsPath = os.osNodeArgs.naTlsPath}
, networkHost              = {getHost = cluster.ccfgRelays}
, networkValency           = {getValency = topology.wallet.wtcfgValency}
, networkFallback          = {getFallback = topology.wallet.wtcfgFallbacks}
, networkTlsca             = {getTlsca = launcher.lTlsca}
, networkTlscert           = {getTlscert = launcher.lTlscert}
, networkTlskey            = {getTlskey = launcher.lTlsKey}
}