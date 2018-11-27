\(cluster : ./cluster.type) ->
\(os      : ./os.type)      ->
{ configuration         =
    { filePath          = os.configurationYaml
    , key               = "${cluster.keyPrefix}_${os.name}"
    , systemStart       = [] : Optional Natural
    , seed              = [] : Optional Natural
    }
, nodeDbPath            = os.pass.nodeDbPath
, nodeLogConfig         = os.pass.nodeLogConfig
, updaterPath           = os.pass.updaterPath
, updaterArgs           = os.pass.updaterArgs
, updateArchive         = os.pass.updateArchive
, logsPrefix            = os.nodeArgs.logsPrefix
, reportServer          = cluster.reportServer

-- Remove this field once x509tool is introduced in Cardano
, x509ToolPath          = os.x509ToolPath

-- XXX: NodeArgs
, tlsca                 = "${os.nodeArgs.tlsPath}/server/ca.crt"
, tlscert               = "${os.nodeArgs.tlsPath}/server/server.crt"
, tlsKey                = "${os.nodeArgs.tlsPath}/server/server.key"
, noClientAuth          = True
, logConsoleOff         = True
, updateServer          = cluster.updateServer
, keyFile               = os.nodeArgs.keyfile
, topology              = os.nodeArgs.topology
, walletDbPath          = os.nodeArgs.walletDBPath
, updateLatestPath      = os.nodeArgs.updateLatestPath
, walletAddress         = "127.0.0.1:0"

-- XXX: this is a workaround for Linux
, updateWithPackage     = True
}