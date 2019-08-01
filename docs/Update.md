# How update is being done in Cardano

This document briefly explains how the update is being done in Cardano.
When we say we are perfoming an update, we're actually running the installer file.

## Daedalus CI creates installer file

The installers are being built by CI for daedalus.
They are available under the sections for:

- Darwin
- Linux-nix
- Windows-nix

There will be artifacts, that contain the installers for each cluster
(mainnet, staging, testnet).

## DevOps propose update on blockchain

When the update is ready, the DevOps will upload the installer file and use
Cardano blockchain to propose an update. This is done by accessing the core
nodes and using [auxx](https://github.com/input-output-hk/cardano-sl/blob/develop/docs/auxx.md)
to submit special message on a blockchain. The effect will take in 12 hours.

## Node signals Daedalus that the update is available

When an update proposal is put into the chain, the hashes for the installers
are put into the blockchain and cardano-node will download the right installer
for the current platform (based on the configuration). The node will then signal
to daedalus that an update is pending.

## Node runs the updater.

Daedalus can let the launcher know that the they are ready to perform an update
by exiting with code `20`.

How the update is being done depends on the operating system the node is running
on.

### Darwin

On Darwin, the update is being done by running `daedalus.pkg` file. Launcher 
will run `/usr/bin/open -FW Installer.pkg` and relaunch itself once the installation
is complete. 

### Linux

On Linux, the update is being done by running bash script `installer.sh`. The location
of the script is based on the configuration (Usually, its located under 
`bin/update-runner`). The script will take care of the installation an re-launch
the wallet once everything is done.

### Windows

On Windows, you cannot perform write on a executable that is running. Because of
this, we must fully stop the launcher before running the installer and instead of
launcher executing the installer, we'll be using batch file `Installer.bat`
which will run the update procedure and re-launch the launcher. The file will be
created by the launcher.