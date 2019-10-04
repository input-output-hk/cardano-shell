# cardano-launcher

`cardano-launcher` is an executable which is used to launch
[Daedalus](https://github.com/input-output-hk/daedalus) as well as handling
restart/exit process.

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

## Manual testing on Windows

`cardano-launcher` have a script that will package everything you need to test the
launcher on Windows platform.

Run the script below and you'll have `updater_test.zip` file located in the `result/`
directory.

```terminal
nix-build updater-test-win.nix
```
