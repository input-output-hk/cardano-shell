\(cluster : ./types/cluster.type) ->
\(os      : ./types/os.type)      ->
{ lConfiguration         =
    { lcfgFilePath          = os.osConfigurationYaml
    , lcfgKey               = "${cluster.ccfgKeyPrefix}_${os.osName}"
    , lcfgSystemStart       = [] : Optional Integer
    , lcfgSeed              = [] : Optional Integer
    }
, lNodeDbPath            = os.osPass.pNodeDbPath
, lNodeLogConfig         = os.osPass.pNodeLogConfig
, lUpdaterPath           = os.osPass.pUpdaterPath
, lUpdaterArgs           = os.osPass.pUpdaterArgs
, lUpdateArchive         = os.osPass.pUpdateArchive
, lLogsPrefix            = os.osNodeArgs.naLogsPrefix
, lReportServer          = cluster.ccfgReportServer

-- Remove this field once x509tool is introduced in Cardano
, lX509ToolPath          = os.osX509ToolPath

-- XXX: NodeArgs
, lTlsca                 = "${os.osNodeArgs.naTlsPath}/server/ca.crt"
, lTlscert               = "${os.osNodeArgs.naTlsPath}/server/server.crt"
, lTlsKey                = "${os.osNodeArgs.naTlsPath}/server/server.key"
, lNoClientAuth          = True
, lLogConsoleOff         = True
, lUpdateServer          = cluster.ccfgUpdateServer
, lKeyFile               = os.osNodeArgs.naKeyfile
, lTopology              = os.osNodeArgs.naTopology
, lWalletDbPath          = os.osNodeArgs.naWalletDBPath
, lUpdateLatestPath      = os.osNodeArgs.naUpdateLatestPath
, lWalletAddress         = "127.0.0.1:0"

-- XXX: this is a workaround for Linux
, lUpdateWithPackage     = True
}