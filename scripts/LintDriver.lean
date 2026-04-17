import Cslib.Init

-- Lake lint driver for absinterp.
-- Invoked by `lake lint`; receives linted module names as args (ignored here
-- since lint-style operates on the whole repo, not per-module).
-- Extend this file to add #lint-style Lean linters when needed.

def runLake (args : Array String) : IO UInt32 := do
  IO.Process.spawn { cmd := "lake", args := args } >>= (·.wait)

def main (_ : List String) : IO UInt32 := do
  IO.println "lint: text style (lint-style)..."
  let styleResult ← runLake #["exe", "lint-style"]
  if styleResult != 0 then
    IO.eprintln "lint failed: lint-style"
    return styleResult
  IO.println "lint: all checks passed"
  return 0
