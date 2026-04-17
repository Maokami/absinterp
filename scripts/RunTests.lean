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

  IO.println "hygiene: warning-free build (--wfail --iofail)..."
  let wfailResult <- runLake #["build", "--wfail", "--iofail"]
  if wfailResult != 0 then
    IO.eprintln "hygiene gate failed: warnings present (fix before merging)"
    return wfailResult

  IO.println "hygiene: text style (lint-style)..."
  let lintStyleResult <- runLake #["exe", "lint-style"]
  if lintStyleResult != 0 then
    IO.eprintln "hygiene gate failed: lint-style"
    return lintStyleResult

  IO.println "all build and hygiene checks passed"
  return 0
