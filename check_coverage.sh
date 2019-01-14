#!/bin/sh

set -euo pipefail

set -x # Enable debugging

#PROJECT_PATH=$(pwd)
# seems we can run only from tmp by default
#cd /tmp
curl -L -v https://github.com/rubik/stack-hpc-coveralls/releases/download/v0.0.4.0/shc-linux-x64-8.0.1.tar.bz2 | tar -xj
#ls -la
which ./shc
#cd $PROJECT_PATH

./shc --repo-token=$COVERALLS_REPO_TOKEN cardano-shell cardano-shell-test

#/tmp/shc --repo-token=$COVERALLS_REPO_TOKEN cardano-shell cardano-shell-test

set +x # Disable debugging

