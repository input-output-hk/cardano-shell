\(cluster : ../types/cluster.type) ->
\(os: ../types/os.type) ->
\(launcher : ../types/launcher.type) ->
\(topology : ../types/topology.type) ->
{ walletDbPath   = os.osNodeArgs.naWalletDBPath
, walletPath     = os.osPass.pWalletPath
, walletLogging  = os.osPass.pWalletLogging
, walletPort     = cluster.ccfgWalletPort
, walletAddress  = launcher.lWalletAddress
, walletRelays   = topology.wallet.wcfgRelays
, walletValency  = topology.wallet.wcfgValency
, walletFallback = topology.wallet.wcfgFallbacks
}