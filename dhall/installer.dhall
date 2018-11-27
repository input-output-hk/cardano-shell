\(cluster : ./cluster.type) ->
\( os : ./os.type) ->
{ installDirectory = os.installDirectory
, walletPort       = cluster.walletPort
}
