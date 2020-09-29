cardano-shell
=============

|Coverage Status|

|"master" Build status|

This is the ``cardano-shell`` project. This project uses Github issues
for tracking the project progress.

About
-----

This "node shell" is a thin layer of functionality surrounding the node.
It's a thin layer which brings all the other modules working together
and makes sure that they have the required resources (configuration,
exception handling, monitoring, logging, ...).

|cardano-shell|

From the top level, the "node shell" contains some of the following:

-  startup initialization
-  configuration loading
-  process monitoring

Some of it responsibilities are the cross-cutting concerns like:

-  logging
-  monitoring
-  configuration
-  exception handling
-  launcher (it's related to startup, but we need to simplify it if
   possible)

|cardano-shell-responsibilities|

For example, we can see some of the modules ``cardano-shell`` integrates
with:

-  network layer
-  blockchain layer
-  ledger layer
-  logging layer
-  monitoring layer
-  wallet (backend) layer

|cardano-shell-integration|

Any module that requires a substantial amount of logging or monitoring,
should provide such resources iself. For example, 1 thread per module
should be enough from the point of view of ``cardano-shell``. If, for
example, ``network`` module requires 5 threads, it should provide such
resources itself.

For serving the module functionality, we can use ``withAsync`` for
top-level calls which is resource/exception safe. The option left for
discussion is whether we should have a need for a restart on a
module/process.

For more info about the architecture, please take a look at
`here <ARCHITECTURE.md>`__. For more info about the launcher, please
take a look at `here <LAUNCHER.md>`__.

Example
-------

For example, we can get a chain generator to try to integrate with
logging output and ``cardano-shell`` should be a piece of code that
glues them together, providing a very simple (random) chain generation
and it's output. We need to remove a lot of things that are there in the
old version. For example, the Servant API.

People
------

Core seems to be split into:

-  blockchain
-  ledger

Currently, the (relevant) team structure seems to be:

-  networking - Duncan
-  core - Eric
-  logging & monitoring - Alexander

Building
--------

You can build the project using Stack or Nix.

Stack
~~~~~

::

   stack build --fast

.. _stack--nix:

Stack + Nix
~~~~~~~~~~~

::

   stack build --fast --nix

Or enable the option for nix building in your local configuration for
Stack.

.. _cabal--nix:

Cabal + Nix
~~~~~~~~~~~

There is an option of using just Cabal + Nix as well - use a small
utility script (watch out, it's a dot before the ``cabal``!) and work as
you would usually if you develop with cabal:

::

   ./cabal new-build

Adding new dependencies can be easy with, for example:

::

   cabal2nix https://github.com/input-output-hk/cardano-prelude --revision "2d6624af423d0a5c7ced6f3ae465eaaeb4ec739e" > cardano-prelude.nix

Tools
-----

You can install multiple tools that can help you, there are configs for
these tools in the project repo:

::

   stack install hindent
   stack install stylish-haskell
   stack install hsimport
   stack install hdevtools

.. |Coverage Status| image:: https://coveralls.io/repos/github/input-output-hk/cardano-shell/badge.svg?branch=HEAD
   :target: https://coveralls.io/github/input-output-hk/cardano-shell?branch=HEAD
.. |"master" Build status| image:: https://badge.buildkite.com/5e4cd5ff2fd87975136914d037c409618deb4d8ed6579f8635.svg?branch=master
   :target: https://buildkite.com/input-output-hk/cardano-shell
.. |cardano-shell| image:: https://user-images.githubusercontent.com/6264437/47286557-70baf200-d5ef-11e8-8fe7-8584a9d6ae44.jpg
.. |cardano-shell-responsibilities| image:: https://user-images.githubusercontent.com/6264437/47286789-736a1700-d5f0-11e8-9056-514101b237f0.jpg
.. |cardano-shell-integration| image:: https://user-images.githubusercontent.com/6264437/47286815-88df4100-d5f0-11e8-92a7-c807b6d3b47a.jpg

Coverage
~~~~~~~~

You can generate a coverage report for the entire project like so:

::

   nix-build -A cardanoShellHaskellPackages.projectCoverageReport --arg config "{ haskellNix = { coverage = true; }; }"

or for each package like this:

::

   nix-build -A cardanoShellHaskellPackages.cardano-shell.coverageReport --arg config "{ haskellNix = { coverage = true; }; }"
   nix-build -A cardanoShellHaskellPackages.cardano-launcher.coverageReport --arg config "{ haskellNix = { coverage = true; }; }"

The CI is currently configured to upload a project coverage report to
a coverage web service. It does this using the script provided by:

::

   $(nix-build -A uploadCoverallsScript --arg config "{ haskellNix = { coverage = true; }; }")/bin/uploadCoveralls.sh
