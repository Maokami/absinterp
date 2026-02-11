import Cslib.Init

def runLake (args : Array String) : IO UInt32 := do
  IO.Process.spawn { cmd := "lake", args := args } >>= (·.wait)

def main (_ : List String) : IO UInt32 := do
  IO.println "building AbsInterpLTS..."
  let buildResult <- runLake #["build"]
  if buildResult != 0 then
    IO.eprintln "build failed"
    return buildResult

  IO.println "building Tests..."
  let testsBuildResult <- runLake #["build", "Tests"]
  if testsBuildResult != 0 then
    IO.eprintln "test build failed"
    return testsBuildResult

  IO.println "bootstrap checks passed"
  return 0
