
Example of usage of 'cardano-shell' in 'cardano-ledger'
=======================================================


The 'validate-mainnet' application in 'cardano-ledger' runs a set of recorded epochs through validation of ledger rules. These epochs are conveniently stored in local files.
The app starts in [Main.hs](https://github.com/input-output-hk/cardano-ledger/blob/master/validate-mainnet/app/Main.hs) with initialisation of configuration and environment:

```
main :: IO ()
main = do
  let cardanoConfiguration = mainnetConfiguration
  cardanoEnvironment <- initializeCardanoEnvironment

```

Then, creates the logging feature:
```
  (loggingLayer, loggingFeature) <- createLoggingFeature
    cardanoEnvironment
    cardanoConfiguration

```

And, creates its own blockchain validation feature:
```
  (blockchainLayer, blockchainFeature) <- createBlockchainFeature
    cardanoEnvironment
    cardanoConfiguration
    Production
    loggingLayer

```

The application will have access to these features, and the functions defined in 'loggingLayer' and 'blockchainLayer':
```
  runCardanoApplicationWithFeatures
      Production
      [blockchainFeature, loggingFeature]
    . CardanoApplication
    $ blockchainApp loggingLayer blockchainLayer

```

Imports and dependencies
------------------------

The main module only imports modules exported by 'Cardano.Shell'. No need to directly import any module from the logging framework, for example.
The features defined in 'Cardano.Shell' provide a structure, or layer, with the exported functions. 

The application's import of 'Cardano.Shell' modules:

```
import Cardano.Shell.Features.Logging
  ( LoggingLayer(..), Trace, createLoggingFeature)
import Cardano.Shell.Lib (runCardanoApplicationWithFeatures)
import Cardano.Shell.Presets (mainnetConfiguration)
import Cardano.Shell.Types
  ( ApplicationEnvironment(..)
  , CardanoApplication(..)
  , initializeCardanoEnvironment
  )

```


Logging support
---------------

The 'LoggingLayer' is a structure that provides most logging functions. And, the types used are re-exported by the 'LoggingFeature'.
A declaration `import Cardano.Shell.Features.Logging` will add them to the local namespace.

The logging is setup and provides a basic trace to which observables can be traced, or from which more named traces can be derived.

The application enters a logging context named "validate-mainnet" by creating a subtrace:
```
blockchainApp :: LoggingLayer -> BlockchainLayer -> IO ()
blockchainApp ll bcl = do
  mainTrace <- llAppendName ll "validate-mainnet" (llBasicTrace ll)

  -- Bulk chain validation
  bulkChainValidation mainTrace bcl ll
```
All subsequent traced observables will be labelled with this name.

The app continues to validate epochs, one epoch file after the other, and outputs logging messages:

```
bulkChainValidation :: Trace IO Text -> BlockchainLayer -> LoggingLayer -> IO ()
bulkChainValidation logTrace bcl ll = do
  logNotice logTrace "Begin validating epoch files..."
  bulkChainValidationLoop logTrace
 where
  logNotice :: Trace IO Text -> Text -> IO ()
  logNotice = llLogNotice ll
```

The `llLogNotice` functions, available from the 'LoggingLayer', outputs a message with severity 'Notice' on the trace.


