import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterpLTS.Core.Semantics

namespace AbsInterpLTS
namespace Core

open Cslib

universe u v

/-- One-step post operator induced by an LTS and a fixed label. -/
def postStep
    {State : Type u}
    {Label : Type v}
    (lts : LTS State Label)
    (label : Label) :
    Post State :=
  fun states => lts.setImage states label

/-- Multi-step post operator induced by an LTS and a label trace. -/
def postTrace
    {State : Type u}
    {Label : Type v}
    (lts : LTS State Label)
    (labels : List Label) :
    Post State :=
  fun states => lts.setImageMultistep states labels

/-- Label-agnostic one-step post operator induced by an LTS. -/
def postAny
    {State : Type u}
    {Label : Type v}
    (lts : LTS State Label) :
    Post State :=
  fun states =>
    { s' : State | exists s : State, s ∈ states ∧ exists label : Label, lts.Tr s label s' }

end Core
end AbsInterpLTS
