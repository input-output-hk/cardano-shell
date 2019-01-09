\(os: ../types/os.type) ->
\(launcher: ../types/launcher.type) ->
{ loggingConfigurationYaml  = os.osConfigurationYaml
, loggingLogPrefix          = os.osNodeArgs.naLogsPrefix
, loggingNodeLogConfig      = os.osPass.pNodeLogConfig
, loggingNodeLogPath        = os.osPass.pNodeLogPath
, loggingWorkingDir         = os.osPass.pWorkingDir
, loggingLauncherLogsPrefix = os.osPass.pLauncherLogsPrefix
, loggingLogConsoleOff      = launcher.lLogConsoleOff
}