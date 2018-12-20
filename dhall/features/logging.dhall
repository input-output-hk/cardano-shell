\(os: ../types/os.type) ->
\(launcher: ../types/launcher.type) ->
{ configurationYaml  = os.osConfigurationYaml
, logPrefix          = os.osNodeArgs.naLogsPrefix
, nodeLogConfig      = os.osPass.pNodeLogConfig
, nodeLogPath        = os.osPass.pNodeLogPath
, workingDir         = os.osPass.pWorkingDir
, walletLogging      = os.osPass.pWalletLogging
, launcherLogsPrefix = os.osPass.pLauncherLogsPrefix
, logConsoleOff      = launcher.lLogConsoleOff
}