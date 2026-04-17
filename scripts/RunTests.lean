import Cslib.Init

def runLake (args : Array String) : IO UInt32 := do
  IO.Process.spawn { cmd := "lake", args := args } >>= (·.wait)

def main (_ : List String) : IO UInt32 := do
  IO.println "building AbsInterp..."
  let buildResult <- runLake #["build"]
  if buildResult != 0 then
    IO.eprintln "AbsInterp build failed"
    return buildResult

  IO.println "building Tests..."
  let testsBuildResult <- runLake #["build", "Tests"]
  if testsBuildResult != 0 then
    IO.eprintln "Tests build failed"
    return testsBuildResult

  IO.println "hygiene: warning-free build (--wfail)..."
  let wfailResult <- runLake #["build", "--wfail"]
  if wfailResult != 0 then
    IO.eprintln "hygiene gate failed: warnings present (fix before merging)"
    return wfailResult

  IO.println "hygiene: lake lint..."
  let lintResult <- runLake #["lint"]
  if lintResult != 0 then
    IO.eprintln "hygiene gate failed: lake lint"
    return lintResult

  IO.println "all build and hygiene checks passed"
  return 0
