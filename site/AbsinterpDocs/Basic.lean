import VersoManual

import AbsinterpDocs.Home
import AbsinterpDocs.Architecture
import AbsinterpDocs.ReadingGuide
import AbsinterpDocs.IMPCollectingShowcase

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "absinterp — layered abstract interpretation in Lean 4" =>
%%%
shortTitle := "absinterp"
authors := ["absinterp contributors"]
%%%

Welcome to the `absinterp` documentation site.
`absinterp` is a Lean 4 repository for reusable abstract-interpretation
infrastructure over CSLib-style labeled transition systems, with IMP as the
main validation case study.

This site collects the design notes, reading paths, and showcase writeups
that live alongside the source tree. The Lean source itself is the
authoritative specification; this site exists to orient readers and
reviewers.

{include 1 AbsinterpDocs.Home}

{include 1 AbsinterpDocs.Architecture}

{include 1 AbsinterpDocs.ReadingGuide}

{include 1 AbsinterpDocs.IMPCollectingShowcase}
