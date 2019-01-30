# Launcher

## Launching

The current way the node launches in production is via Daedalus.
The Daedalus launches the node and communicates via the `node-ipc` what port to pick for the node to start working on.
After they are in sync, they continue the communication via the default REST API.

## Update

The update system is pretty complicated. The update hash is read from the blockchain and then the node tries to find that update hash and download it from the update server (there is a parameter which we use for the update server URL).
There is the script-runner, the tool, with which we can use to see how the updates happen in "real-time".
The source of most of that update logic can be found in `cardano-auxx`.

## Daedalus

- is the integration using Injections?
- a menu for selecting the network?
- any suggestions for improving the way it currently works?

