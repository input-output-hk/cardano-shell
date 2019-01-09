\(os: ../types/os.type) ->
{ blockchainConfigurationYaml = os.osConfigurationYaml
, blockchainKeyFile           = os.osNodeArgs.naKeyfile
, blockchainStatePath         = os.osPass.pStatePath
, blockchainNodePath          = os.osPass.pNodePath
, blockchainNodeDbPath        = os.osPass.pNodeDbPath
}