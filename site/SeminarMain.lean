import VersoManual
import AbsinterpSlides

open Verso.Genre.Manual

def config : Config := {
  sourceLink := some "https://github.com/Maokami/absinterp"
  issueLink := some "https://github.com/Maokami/absinterp/issues"
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  destination := "_out/seminar"
  htmlDepth := 1
}

def main := manualMain (%doc AbsinterpSlides.Seminar) (config := { config with })
