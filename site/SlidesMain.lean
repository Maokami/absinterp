import VersoManual
import AbsinterpSlides

open Verso.Genre.Manual

/--
Emit the single-file talk deck under `_out/slides`, which the GitHub Pages
workflow republishes under `/slides/`.
-/
def config : Config := {
  sourceLink := some "https://github.com/Maokami/absinterp"
  issueLink := some "https://github.com/Maokami/absinterp/issues"
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  destination := "_out/slides"
  htmlDepth := 1
}

def main := manualMain (%doc AbsinterpSlides.Intro) (config := { config with })
