\(cluster : ./types/cluster.type) ->
{ wallet = {
      wtcfgRelays    = [[{ getHost = cluster.ccfgRelays }]]
    , wtcfgValency   = +1
    , wtcfgFallbacks = +7
  }
}