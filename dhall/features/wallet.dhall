\(cluster : ../types/cluster.type) ->
\(os: ../types/os.type) ->
\(launcher : ../types/launcher.type) ->
\(topology : ../types/topology.type) ->
{ walletDbPath   = { getDbPath = os.osNodeArgs.naWalletDBPath }
, walletPath     = { getWalletPath = os.osPass.pWalletPath }
, walletLogging  = { getWalletLogging = os.osPass.pWalletLogging}
, walletPort     = { getWalletPort = cluster.ccfgWalletPort}
, walletAddress  = { getWalletAddress = launcher.lWalletAddress }
, walletRelays   = { getWalletRelays = topology.wallet.wtcfgRelays}
, walletValency  = { getWalletValency = topology.wallet.wtcfgValency}
, walletFallback = { getWalletFallback = topology.wallet.wtcfgFallbacks}
}