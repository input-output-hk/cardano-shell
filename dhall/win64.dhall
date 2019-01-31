\(cluster : ./types/cluster.type)      ->
   let installDir = "Daedalus${cluster.ccfgInstallDirectorySuffix}"
in let dataDir = "\${APPDATA}\\${installDir}"
    --
    --
in
{ osName      = "win64"
, osConfigurationYaml  = "\${DAEDALUS_INSTALL_DIRECTORY}\\configuration.yaml"
, osInstallDirectory   = installDir
, osX509ToolPath       = "\${DAEDALUS_DIR}\\cardano-x509-certificates.exe"
, osNodeArgs           =
  { naKeyfile          = "Secrets-1.0\\secret.key"
  , naLogsPrefix       = "Logs"
  , naTopology         = "\${DAEDALUS_DIR}\\wallet-topology.yaml"
  , naUpdateLatestPath = "Installer.exe"
  , naWalletDBPath     = "Wallet-1.0"
  , naTlsPath          = "tls"
  }
, osPass      =
  { pStatePath           = dataDir
  , pWorkingDir          = dataDir
  , pNodePath            = "\${DAEDALUS_DIR}\\cardano-node.exe"
  , pNodeDbPath          = "DB-1.0"
  , pNodeLogConfig       = "\${DAEDALUS_INSTALL_DIRECTORY}\\log-config-prod.yaml"
  , pNodeLogPath         = [] : Optional Text
  , pWalletPath          = "\${DAEDALUS_DIR}\\Daedalus.exe"
  , pWalletLogging       = True
  , pFrontendOnlyMode    = True

  , pUpdaterPath         = "Installer.exe"
  , pUpdaterArgs         = [] : List Text
  , pUpdateArchive       = [] : Optional Text
  , pUpdateWindowsRunner = ["Installer.bat"] : Optional Text

  , pLauncherLogsPrefix  = "Logs\\pub"
  }
}
