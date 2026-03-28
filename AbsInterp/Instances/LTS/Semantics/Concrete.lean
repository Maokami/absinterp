import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterp.Framework.Semantics.Concrete

namespace AbsInterp
namespace Instances
namespace LTS

open Cslib
open AbsInterp.Framework

universe u v

/-- One-step post operator induced by an LTS and a fixed label. -/
def postStep
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (label : Label) :
    Post State :=
  fun states => lts.setImage states label

/-- Multi-step post operator induced by an LTS and a label trace. -/
def postTrace
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (labels : List Label) :
    Post State :=
  fun states => lts.setImageMultistep states labels

end LTS
end Instances
end AbsInterp
