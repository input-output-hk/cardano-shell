\(os: ../types/os.type) ->
{ configurationYaml = os.osConfigurationYaml
, keyFile           = os.osNodeArgs.naKeyfile
, walletDBpath      = os.osNodeArgs.naWalletDBPath
, statePath         = os.osPass.pStatePath
, nodePath          = os.osPass.pNodePath
, nodeDbPath        = os.osPass.pNodeDbPath
}