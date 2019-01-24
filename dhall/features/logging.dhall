\(os: ../types/os.type) ->
\(launcher: ../types/launcher.type) ->
{ loggingConfigurationYaml  = {getConfigurationYamlPath = os.osConfigurationYaml}
, loggingLogPrefix          = {getLogPrefix = os.osNodeArgs.naLogsPrefix}
, loggingNodeLogConfig      = {getNodeLogConfig = os.osPass.pNodeLogConfig}
, loggingNodeLogPath        = {getNodeLogPath = os.osPass.pNodeLogPath}
, loggingWorkingDir         = {getWorkingDir = os.osPass.pWorkingDir}
, loggingLauncherLogsPrefix = {getLauncherLogsPrefix = os.osPass.pLauncherLogsPrefix}
, loggingLogConsoleOff      = {getLogConsoleOff = launcher.lLogConsoleOff}
}