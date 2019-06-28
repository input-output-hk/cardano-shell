# Overview

`cardano-shell` is a thin layer which brings all the other modules working
together and makes sure that they have the required resources 
(configuration, exception handling, ...).

## Cardano-node to operate as an peer

For cardano-node to operate as an peer, various **features** are required:

* Logging, to let the user know what's going on
* Block validation
* Managing blockchain/stake
* Communicating with other peers
* Submitting transaction
* Providing interface/API so that the user can interact with the node

and so on. Because of this, IOHK currently has multiple development teams, 
each of which is responsible for developing specific features.

* [blockchain layer](https://github.com/input-output-hk/cardano-ledger)
* [ledger layer](https://github.com/input-output-hk/cardano-ledger)
* [logging/monitoring layer](https://github.com/input-output-hk/iohk-monitoring-framework)
* [network layer](https://github.com/input-output-hk/ouroboros-network)
* [wallet backend layer](https://github.com/input-output-hk/cardano-wallet)

### Bringing features together

The thing to note is that all these features are being worked on **seperate**
repository. 

![scattered-modules](https://user-images.githubusercontent.com/15665039/55607001-dbcf3e00-57b5-11e9-89bf-9ed403c4e8e6.jpg)

We need these modules working together to act as a node. This is where 
`cardano-shell` comes in. The shell will act as a **glue** of these features,
providing required resources/configurations to each of these features as well as
resolving its dependencies.

![shell-diagram](https://user-images.githubusercontent.com/6264437/47286815-88df4100-d5f0-11e8-92a7-c807b6d3b47a.jpg)

## Resolving dependencies between the features

There are **dependencies** between the features meaning some of the features
 depend on others. For example,

* `networking` feature requires `logging` and `monitoring`
* `blockchain` feature `logging` and `networking`

and so on.

The shell will resolve these dependencies by having each of the features to
 produce a `layer` and distributing them to other features that depend on it.

### Layer

To put it simple, **a layer is a record of functions that each feature generates when initialized**. 
For example, logging feature will produce logging layer when initialized.
The logging layer will have a list of functions related to logging such as
`logInfo`, `logDebug` which the other features can use.

![layer](https://user-images.githubusercontent.com/15665039/55375129-e1bee800-5545-11e9-82c0-f7bef87deaf3.jpg)

Dependencies between the features are resolved by passing these layers. 

- If `networking` feature requires `logging`, then it will have logging
layer as a dependency when initializing.

![network](https://user-images.githubusercontent.com/15665039/55375015-7f65e780-5545-11e9-9fd8-ca2d37d7cc28.jpg)

- If `blockchain` feature requires `logging` and `network`, then shell will
provide those layers as dependencies.

![blockchain](https://user-images.githubusercontent.com/15665039/55375281-8a6d4780-5546-11e9-9240-21d9ca8cbc46.jpg)

Layers are defined in such a way that it can be **stubbed**. This will 
allow the developer to write test cases on each features with ease.
