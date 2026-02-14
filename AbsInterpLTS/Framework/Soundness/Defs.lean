import Cslib.Init

import AbsInterpLTS.Framework.Semantics.Concrete.Defs
import AbsInterpLTS.Framework.Semantics.Abstract.Defs

namespace AbsInterpLTS
namespace Framework

universe u v w

/-!
# Soundness Interfaces

This file defines one-step and trace-level soundness predicates linking
concrete and abstract semantic transformers via concretization `Gamma`.
-/

abbrev Gamma (Abstract : Type u) (State : Type v) := Abstract -> Set State

/--
Core soundness direction:
`post (gamma a) ⊆ gamma (postAbs a)`.
-/
def Sound
    {State : Type u}
    {Abstract : Type v}
    (post : Post State)
    (gamma : Gamma Abstract State)
    (postAbs : PostSharp Abstract) : Prop :=
  forall a : Abstract, post (gamma a) ⊆ gamma (postAbs a)

/--
One-step soundness for label-indexed transformers:
`stepPost label (gamma a) ⊆ gamma (postAbs label a)`.
-/
def SoundStep
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    (stepPost : Label -> Post State)
    (gamma : Gamma Abstract State)
    (postAbs : StepPostSharp Abstract Label) : Prop :=
  forall label : Label, forall a : Abstract,
    stepPost label (gamma a) ⊆ gamma (postAbs label a)

/--
Trace-level soundness for trace-indexed transformers:
`tracePost labels (gamma a) ⊆ gamma (postAbs labels a)`.
-/
def SoundTrace
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    (tracePost : List Label -> Post State)
    (gamma : Gamma Abstract State)
    (postAbs : TracePostSharp Abstract Label) : Prop :=
  forall labels : List Label, forall a : Abstract,
    tracePost labels (gamma a) ⊆ gamma (postAbs labels a)

end Framework
end AbsInterpLTS
