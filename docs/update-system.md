## Update system notes

These are notes on how the wallet update system currently works.

They can be used as the basis for the update system design of `cardano-shell`.

### Diagram

This is the `frontendOnlyScenario` from `cardano-sl/tools/src/launcher/Main.hs`.
Do not worry about `serverScenario` - replace it completely.

The Daedalus install is always configured to run the launcher in
`frontendOnlyMode`. The other code (`clientScenario`) is dead
code. The diagram describes `frontendOnlyMode`, which goes through the
`node-ipc` system.

![sequence-chart](update-system.png)

#### Running the update system

The very first thing that `cardano-launcher` does, before starting the
frontend, is check for a previously downloaded update.

If there is a file at `updaterPath`, it runs the updater, which is a
bit wrong.

There are two code paths, depending on whether launcher is running on Windows.

##### macOS and Linux

To run the updater on non-Windows systems, it will spawn
`${updaterPath} ${updaterArgs} ${updateArchive}`.

After the update subprocess exits successfully, it hashes the
`updateArchive` file, checks that the wallet database has this hash,
then deletes the `updateArchive` file.

##### Windows

To run the updater on Windows systems, it will create a `.bat` file
then execute it. The temporary `.bat` file runs the following steps:

1. Kill the `cardano-launcher` process with `TaskKill /PID`
2. Run the downloaded installer for the new version.
3. Delete the installer file.
4. Run `cardano-launcher` with the same command line arguments that
   the previous launcher was run with.
5. Delete the `.bat` file.

#### Starting `cardano-node`

Daedalus spawns the `cardano-node` process using
[child_process](https://nodejs.org/api/child_process.html). It then
uses the nodejs API to pass "messages" to the subprocess (see
`cardano-sl/node-ipc/src/Cardano/NodeIPC.hs`).


#### Applying updates

To apply an update, `cardano-launcher` just loops back to the start,
where the update system will immediately run.


### New design

The old design can be simplified and improved on.

#### In scope for `cardano-shell`

- Responds correctly when Daedalus exits with status 20 (user chose to apply update).

- Responds correctly when Daedalus exits with status 21 or 22.

- Works on Windows. Note the possible portability issues surrounding:
   - Output redirection
   - Exclusive file locking
   - Paths
   - Killing processes
   - Different installation methods

- Works on Linux for single-file executable containers such as
  AppImage or Snap. These executable formats require that the
  `cardano-launcher` process be terminated and restarted for updates.

#### Out of scope for `cardano-shell`

- Update system for nodes which aren't running inside Daedalus. For
  example, exchange wallets and staking nodes. These users will handle
  updating their node software.

- Sending node crash reports to report-server. Nobody looks at
  these. Daedalus has its own crash reporting feature.

#### Questions

- Is it necessary to have two processes `cardano-launcher` and
  `cardano-node`, or can they be combined?

- Is there a more "standard" way for electron apps to start their
  backend servers?

