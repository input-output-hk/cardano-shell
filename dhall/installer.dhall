\(cluster : ./types/cluster.type) ->
\( os : ./types/os.type) ->
{ icfgInstallDirectory = os.osInstallDirectory
, icfgWalletPort       = cluster.ccfgWalletPort
}
