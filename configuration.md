# configuration.yaml Variables

    "block"
      - networkDiameter - Estimated time for broadcasting messages
        Note: Varies between mainnet and dev
      - recoveryHeadersMessage - Numbers of headers put in message in recovery mode. Should be greater than k.
        Note: dev_block = 20, mainnet_base_block = 2200
      - streamWindow - Number of blocks to have inflight.
        Note: dev_block & mainnet_base_block = 2048
      - nonCriticalCQBootstrap - If chain quality in bootstrap era is less than this value, non critical misbehavior will be reported
        Note: dev_block & mainnet_base_block = 0.95
      - criticalCQBootstrap - If chain quality after bootstrap era is less than this value, critical misbehavior will be reported.
        Note: dev_block & mainnet_base_block = 0.8888
      - nonCriticalCQ - If chain quality after bootstrap era is less than this value, non critical misbehavior will be reported.
        Note: dev_block & mainnet_base_block = 0.8
      - criticalCQ - If chain quality after bootstrap era is less than this value, critical misbehavior will be reported.
        Note: dev_block & mainnet_base_block = 0.654321
      - criticalForkThreshold - Number of blocks such that if so many blocks are rolled back, it requires immediate reaction
        Note: dev_block = 2 mainnet_base_block = 3
      - fixedTimeCQ - Chain quality will be also calculated for this amount of seconds.
        Note: dev_block = 10 mainnet_base_block = 3600
    "core"
      - Genesis Configuration - specifies which addresses initially have ADA and how much.
        - avvmDistr - contains AVVM addresses with corresponding balances -  a map from AVVM addresses to balances.
        Note: Appears to be Mainnet AVVM distribution or an empty set. 
        -  initializer - Prefills various values to properly initialize networks, used often in testnet.
        - BlockVersionData - xontains fundamental blockchain-related values
          - heavyDelThd - heavyweight delegation threshold
          - maxBlockSize - maximum size of block, in bytes
          - maxHeaderSize - maximum size of block’s header, in bytes
          - maxProposalSize - maximum size of Cardano SL update proposal, in bytes
          - maxTxSize - maximum size of transaction, in bytes
          - mpcThd - threshold for participation in SSC (shared seed computation)
          - scriptVersion - script version
          - slotDuration - slot duration, in milliseconds
          - softforkRule - rules for softfork
            - initThd - initial threshold, right after proposal is confirmed
            - minThd - minimal threshold (i.e. threshold can’t become less than this one)
            - thdDecrement - theshold will be decreased by this value after each epoch
          - txFeePolicy - transaction fee policy’s values
            - multiplier - 
            - summand
          - unlockStakeEpoch - unlock stake epoch after which bootstrap era ends
          - updateImplicit -  update implicit period, in slots
          - updateProposalThd - threshold for Cardano SL update proposa
          - updateVoteThd - threshold for voting for Cardano SL update proposal.
        - bootStakeHolders - contains bootstrap era stakeholders’ identifiers (StakeholderIds) with corresponding weights
          - [addresses]
        - ftsSeed - base64-encoded contains seed value required for Follow-the-Satoshi mechanism (hex-encoded)
        - nonAvvmBalances - a map from Cardano-SL addresses to balances
        - protocolConsts - contains basic protocol constants
          - k - security parameter from the paper
          - protocolMagic - protocol magic section, described fully below, can either be an object with the two fields described above, or just a plain integer - mainnet: 764824073
            - pm - protocol magic number. When the protocol magic is changed, all signatures become invalid. This is used to distinguish different networks.
            - requiresNetworkMagic - either "NMMustBeNothing" or "NMMustBeJust"
          - vssMaxTTL - VSS certificates maximum timeout to live (number of epochs),
          - vssMinTTL - VSS certificates minimum timeout to live (number of epochs)
        - heavyDelegation - contains an information about heavyweight delegation
          - [address]
            - cert - delegation certificate
            - delegatePk - delegate’s public key
            - issuerPk - stakeholder’s (issuer’s) public key
            - omega - index of epoch the block PSK is announced in, it is needed for replay attack prevention, can be set to arbitrary value in genesis
        - startTime - timestamp of the 0-th slot. Ideally it should be few seconds later than the cluster actually starts. system start time is taken from command line option
        - vssCerts - #Note: This section may not be necessary for OBFT
          - [address]
            - expiryEpoch - index of epoch until which (inclusive) the certificate is valid;
            - signature - signature of certificate
            - signingKey - key used for signing,
            - vssKey - VSS public key.
    "dlg",
      - dlgCacheParam -  This value parameterizes size of cache used in Delegation.
      - messageCacheTimeout - Interval we ignore cached messages in components that support caching
    "node",
      - NetworkConnectionTimeout - Network connection timeout in milliseconds
      - ConversationEstablishTimeout - Conversation acknowledgement timeout in milliseconds
      - BlockRetrievalQueueSize - Block retrieval queue capacity
      - PendingTxResubmissionPeriod - Minimal delay between pending transactions resubmission
      - WalletProductionApi - Whether hazard wallet endpoint should be disabled
      - WalletTxCreationDisabled - Disallow transaction creation or re-submission of pending transactions by the wallet
      - ExplorerExtendedApi - Enable explorer extended API for fetching more info about addresses (like utxos) and bulk endpoints
    "ntp"
      - responseTimeout - time before response is timedout
      - pollDelay - delay between polls of ntp server
      - servers - DNS names for NTP servers
    "ssc" - #Note: This section may not be necessary for OBFT
      - mpcSendInterval - Length of interval during which node should send her MPC message. Relevant only for one SSC implementation.
      - mdNoCommitmentsEpochThreshold - Number of epochs used by malicious actions detection to check if our commitments are not included in blockchain.
    "tls" - Contains info for generating CA and Server self-signed certs
    # Note: Certificates - The CA, server and client certs are generated by GenCerts, which is run when SL launches initially. According to devops, the certs were used in order to prevent multiple daedelus clients from the same machine connecting over loopback to the same SL instance. I noticed that bitcoin and ethereum both do not design for this feature in mind, and that a number of users have issues with TLS not working correctly, so perhaps having a default of no TLS or using pipes would be better (confirmed by . The response suggested that TLS issues are no longer common and that the security benefits outweigh any remianing concerns, but that further analysis of issues is warranted.
    "txp"
      - ccMemPoolLimitTx - Limit on the number of transactions that can be stored in the mem pool
    "update"
      - applicationName - Name of this application.
      - Application Version - Last known block version
      - applicationVersion - Application version
      - lastKnownBlockVersion - System tag
    "wallet"
      - throttle - contains variables for throttling wallet requests and debouncing 