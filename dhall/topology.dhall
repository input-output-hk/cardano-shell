\(cluster : ./cluster.type) ->
{ wallet = {
      wcfgRelays    = [[{ host = cluster.ccfgRelays }]]
    , wcfgValency   = +1
    , wcfgFallbacks = +7
  }
}