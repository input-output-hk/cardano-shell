// This process implicitly sets env varibale "NODE_CHANNEL_FD" with a fd it currently uses
const child_process = require("child_process");
const fs            = require('fs');

// Filepath to resources
const testDir = "test-state";
const logPath = "test-state/cardano-node.log"

// Acquiring resources
function acquire () {
  if (!fs.existsSync(testDir)) {
    fs.mkdirSync(testDir);
  };
  
  let writeStream = fs.createWriteStream(logPath, { flags: "a" }); 
  return writeStream;
}

// Clean up resources
function cleanup () {
  fs.unlinkSync(logPath);
  fs.rmdirSync(testDir);
};

// Return Subprocess with given writeStream and timerid
function getSubProcess(writeStream, timerid) {
  const subproc = child_process.spawn("stack", [
        "exec"
      , "node-ipc"
    ], {
      stdio: [ "inherit", writeStream, writeStream, "ipc" ]
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
      cleanup();
    });
    subproc.on("exit", function (code, signal) {
      console.log(new Date(), "child exited", code, signal);
      cleanup();
      clearTimeout(timerid);
      if (code == 20) {
        process.exit(0);
      } else {
        process.exit(-1);
      }
    });

  return subproc;
}

// Actual process
// I honestly don't know if this can clean-up the resources if async exception occurs
console.log(new Date(), "in parent")
let logfile = acquire ();

logfile.on("open", function () {
  let timerid;
  let subprocess = getSubProcess(logfile, timerid);

  // Action
  console.log(new Date(), "log file opened");
  subprocess.send({QueryPort:[]});
  
  timerid = setTimeout(function () {
    //process.exit();
    console.log(new Date(), "sending disconnect");
    subprocess.disconnect();
    timerid = setTimeout(function () {
      console.log(new Date(), "it failed to exit, killing");
      subprocess.kill();
    },30000);
  }, 30000);
});