#!/usr/bin/env node

// This runs the daedalus-ipc executable in the same way that Daedalus would run cardano-wallet.
// It needs node and daedalus-ipc on the PATH to run.

const child_process = require("child_process");
const http = require('http');

function main() {
  let port = process.argv[2];
  const proc = child_process.spawn("daedalus-ipc", [port],
    { stdio: ["ignore", "inherit", "inherit", "ipc"] }
  );

  proc.on("close", function(code, signal) {
    console.log("JS: child_process stdio streams closed");
    process.exit(2);
  });

  proc.on("disconnect", function() {
    console.log("JS: child_process disconnected");
    process.exit(3);
  });

  proc.on("error", function(err) {
    console.log("JS: error child_process: " + err);
    process.exit(4);
  });

  proc.on("exit", function(code, signal) {
    console.log("JS: child_process exited with status " + code + " or signal " + signal);
    process.exit(5);
  });

  proc.on("message", function(msg) {
    console.log("JS: message received", msg);
    // See CardanoNode.js in Daedalus for the message types in use.
    if (msg.Started) {
      console.log("JS: sending a bogus message");
      proc.send("hello");
    } else if (msg.ParseError && msg.ParseError.match(/encountered String/)) {
      console.log("JS: sending QueryPort");
      proc.send({ QueryPort: [] });
    } else if (msg.ParseError) {
      console.log("JS: i did not expect that");
      process.exit(6);
    } else if (msg.ReplyPort) {
      console.log("JS: received ReplyPort " + msg.ReplyPort + ", expecting " + port);
      process.exit(msg.ReplyPort == port ? 0 : 1);
    }
  });
}

main();
