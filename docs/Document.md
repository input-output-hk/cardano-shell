 # Overview

`cardano-shell` is an thin layer which brings all the other modules working together and makes sure that they have the required resources (configuration, exception handling, monitoring, logging, ...).

The shell is also responsible for:
* Logging
* Monitoring
* Configuration
* Exception handling
* Launcher

## Features

Various **features** are required for the cardano node to operate.

* Blockchain
* Ledger
* Logging
* Monitoring
* Network
* Wallet backend

The shell will act as an **glue** of these features. It provides required resources/configurations to each of these features as well as resolving its dependencies.

## Resolving dependencies between the features

There are **dependencies** between the features meaning some of the features depend on others. For example,

* `networking` feature requires `logging` and `monitoring`
* `blockchain` feature `logging` and `networking`

and so on.

The shell will resolve these dependencies by having each of the features to produce a `layer` and distributing them to other features that depend on it.

### Layer

To put it simple, **a layer is a list of functions that each feature generates whn initialized.**. For example, logging feature will produce logging layer when initialized. The logging layer will have a list of functions related to logging such as `logError`, `logNotice` which the other features can use.

Dependencies between the features are resolved by passing these layers. 

- If `networking` feature requires `logging` features, then it will have logging layer as a dependency when initializing.
- If `blockchain` feature requires `logging` and `network`, then shell will provide those layers as dependencies.

Layers are defined in such a way that it can be **stubbed**. This will enable the developer to implement test each of the features with ease.