import VersoManual
import AbsinterpDocs

open Verso.Genre.Manual

/--
Emit the multi-page documentation site into the default `_out/html-multi`
layout. The GitHub Pages workflow publishes this tree at the site root.
-/
def config : Config := {
  sourceLink := some "https://github.com/Maokami/absinterp"
  issueLink := some "https://github.com/Maokami/absinterp/issues"
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
}

def main := manualMain (%doc AbsinterpDocs.Basic) (config := { config with })
