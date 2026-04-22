import VersoManual
import AbsinterpDocs

open Verso.Genre.Manual

def config : Config := {
  sourceLink := some "https://github.com/Maokami/absinterp"
  issueLink := some "https://github.com/Maokami/absinterp/issues"
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
}

def main := manualMain (%doc AbsinterpDocs.Basic) (config := { config with })
