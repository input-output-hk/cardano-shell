# cardano-launcher

`cardano-launcher` is an executable which is used to launch
[Daedalus](https://github.com/input-output-hk/daedalus) as well as handling
restart/exit process.

The high-level overview:

![launcher_updater_flowchart](https://user-images.githubusercontent.com/6264437/66833560-54c90280-ef5c-11e9-95cf-df8f9a1eb9dc.jpeg)

Key responsibilities include:

1. Generate TLS certificates that are needed for Daedalus to communicate with [cardano-wallet](https://github.com/input-output-hk/cardano-wallet).
2. Setup environment variables that are needed for Daedalus to run.
3. Launching Daedalus wallet as well as handling restart/exit process.
4. Restart Daedalus in GPU-safe mode.
4. Run an update system. For more details about how update is being done, please see
[wiki](https://github.com/input-output-hk/cardano-shell/wiki/How-update-is-being-done-in-Cardano)

### What it does

`cardano-launcher` will first setup environment variables that are needed for
Daedalus to run. It then generates TLS certificates that Daedalus uses to
communicate with `cardano-wallet`. After that, `cardano-launcher` will spawn
Daedalus as a child process. Depending on how Daedalus exits, `cardano-launcher`
will perform restart process, then run Daedalus again. Restart process includes:

1. Running update system when user asks Daedalus to run update.
2. Switching between GPU-safe mode and Normal mode.

When Daedalus exits, the launcher will clean itself up, and exits along with
Daedalus.

## Developing `cardano-launcher`

1. Go into nix-shell by running `nix-shell` command
2. Build the project with stack `stack build --nix`

## Generating `cardano-launcher` executable

### Using stack + nix

1. Go into nix-shell: `nix-shell`
2. Build the project with stack: `stack build --nix`
3. Run `stack install` command to build `cardano-launcher` executable

```terminal
stack --nix install cardano-launcher:cardano-launcher --local-bin-path path/to/bin
```

### Perform cross-compilation

`cardano-launcher` is also capabale of generating portable Windows executable 
on Linux machine by using `nix-build` command.

1. Run the script below.

```terminal
nix-build release.nix -A nix-tools.cexes.x86_64-pc-mingw32-cardano-shell.cardano-launcher.x86_64-linux
```

2. If the build is successful, there should be a `cardano-launcher.exe` file in the 
`result/bin/` directory.

## Stubbing the exit codes for the wallet and the updater (AKA state machine testing)

`cardano-launcher` has the support for stubbing out the wallet and the updater.
This enables controlled testing and supports QA and people who want to see how it behaves without
actually providing all the required environment and configuration.

```
                                               +------------------------+
                                               |                        |
                                               |                        |
                                               |                        |
                           +------------------>+        Wallet          |
                           |                   |                        |
                           |                   |                        |
                           |                   |                        |
                           |                   |                        |
+--------------------------+                   +------------------------+
|                          |
|                          |
|                          |
|                          |
|                          |
|        Launcher          |
|                          |
|                          |
|                          |
|                          |
|                          |
|                          |
+--------------------------+                 +---------------------------+
                           |                 |                           |
                           |                 |                           |
                           |                 |                           |
                           |                 |                           |
                           +---------------->+          Updater          |
                                             |                           |
                                             |                           |
                                             |                           |
                                             |                           |
                                             |                           |
                                             +---------------------------+

```

We can simply imagine that we stub out the wallet and the updater with a list of exit codes.

So when we run something like:
```
stack exec cardano-launcher -- --config ./cardano-launcher/configuration/launcher/launcher-config.demo.yaml --wallet-exit-codes "[CLIExitCodeFailure 21, CLIExitCodeFailure 22, CLIExitCodeFailure 20, CLIExitCodeSuccess]" --updater-exit-codes "[CLIExitCodeFailure 1, CLIExitCodeSuccess]"
```

We stub out both the wallet and the updater with a list of exit codes we defines.
So the first time we run the wallet, the wallet will return the first exit code.
When we run it the second time, the wallet will return the second exit code.
And so on.
After the fourth time (there are 4 exit codes) the real wallet execution will be run
and the exit code we get will be from the actual wallet execution.

It works the same for the updater. It will return stubbed exit codes in order until
it exhaust the exit codes and then it will run the actual updater function.

_If we don't define either of both of these, the real function will be used._

## Manual testing on Windows

`cardano-launcher` have a script that will package everything you need to test the
launcher on Windows platform.

Run the script below and you'll have `updater_test.zip` file located in the `result/`
directory.

```terminal
nix-build updater-test-win.nix
```


