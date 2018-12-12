\(cluster : ./cluster.type) ->
\( os : ./os.type) ->
{ icfgInstallDirectory = os.osInstallDirectory
, icfgWalletPort       = cluster.ccfgWalletPort
}
