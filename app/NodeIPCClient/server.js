// How to run the script:
// Node JS version: v11.10.1
// Have everything built beforehand
// On console, run: "node app/NodeIPCClient/server.js"

// This process implicitly sets environment varibale "NODE_CHANNEL_FD" with a fd it currently uses
// Hakell node will then lookup that fd, and use it to communicate with this script.
const child_process = require("child_process");

// Return Subprocess with given timerid
function getSubProcess( timerid) {
  const subproc = child_process.spawn("node-ipc", [
     "js"
    ], {
      stdio: [ "inherit", "inherit", "inherit", "ipc" ]
    });
    subproc.on("message", function (msg) {
      console.log(new Date(), "got reply",msg);
    });
    subproc.on("close", function(code, signal) {
      console.log("all stdio to child has been closed", code, signal);
    });
    subproc.on("disconnect", function() {
      console.log(new Date(), "all IPC handles closed");
    });
    subproc.on("error", function (err) {
      console.log("error:", err);
    });
    subproc.on("exit", function (code, signal) {
      console.log(new Date(), "child exited", code, signal);
      clearTimeout(timerid);
      if (code == 0) {
        process.exit(0);
      } else {
        process.exit(-1);
      }
    });

  return subproc;
}

// Actual process
// I honestly don't know if this can clean-up the resources if async exception occurs

let timerid;
let subprocess = getSubProcess(timerid);

// Action
console.log(new Date(), "in parent");
console.log(new Date(), "log file opened");
subprocess.send({QueryPort:[]});

timerid = setTimeout(function () {
  console.log(new Date(), "sending disconnect");
  subprocess.disconnect();
  timerid = setTimeout(function () {
    console.log(new Date(), "it failed to exit, killing");
    subprocess.kill();
  },30000);
}, 30000);
