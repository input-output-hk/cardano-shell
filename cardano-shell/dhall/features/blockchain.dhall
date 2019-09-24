\(os: ../types/os.type) ->
{ blockchainConfigurationYaml = {getConfigurationYamlPath = os.osConfigurationYaml}
, blockchainKeyFile           = {getKeyFile = os.osNodeArgs.naKeyfile}
, blockchainStatePath         = {getStatePath = os.osPass.pStatePath}
, blockchainNodePath          = {getNodePath = os.osPass.pNodePath}
, blockchainNodeDbPath        = {getNodeDbPath = os.osPass.pNodeDbPath}
}