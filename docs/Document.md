 # `cardano-shell` overview

`cardano-shell` is an thin layer which brings all the other modules working
 together and makes sure that they have the required resources 
 (configuration, exception handling, monitoring, logging, ...).

The shell is also responsible for:

* Logging
* Monitoring
* Configuration
* Exception handling
* Launcher

## Features

Various **features** are required for the cardano node to operate.

* Blockchain layer
* Ledger layer
* Logging layer
* Monitoring layer
* Network layer
* Wallet backend layer

The shell will act as a **glue** of these features. It provides required
 resources/configurations to each of these features as well as resolving its dependencies.

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

To put it simple, **a layer is a list of functions that each feature generates when initialized.**. 
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
enable the developer to implement test each of the features with ease.
