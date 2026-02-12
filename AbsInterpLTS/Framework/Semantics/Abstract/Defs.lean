import Cslib.Init

import AbsInterpLTS.Framework.Semantics.TraceLift

namespace AbsInterpLTS
namespace Framework

universe u v

/-!
# Abstract Semantic Transformers

This file mirrors concrete trace lifting at the abstract level.

For `postAbs : Label -> (Abstract -> Abstract)`,
`liftTracePostSharp postAbs` composes abstract step transformers left-to-right
along a label list.
-/

/-- Abstract semantic transformer on abstract states. -/
abbrev PostSharp (Abstract : Type u) := Abstract -> Abstract

/-- Label-indexed one-step abstract transformers. -/
abbrev StepPostSharp (Abstract : Type u) (Label : Type v) := Label -> PostSharp Abstract

/-- Trace-indexed abstract transformers. -/
abbrev TracePostSharp (Abstract : Type u) (Label : Type v) := List Label -> PostSharp Abstract

/-- Sequential composition of abstract transformers. -/
def composePostSharp
    {Abstract : Type u}
    (postAbs1 postAbs2 : PostSharp Abstract) :
    PostSharp Abstract :=
  fun a => postAbs2 (postAbs1 a)

/--
Lift one-step abstract transfers to trace transfers by left-to-right composition.
-/
def liftTracePostSharp
    {Abstract : Type u}
    {Label : Type v}
    (postAbs : StepPostSharp Abstract Label) :
    TracePostSharp Abstract Label :=
  liftTrace composePostSharp (fun a => a) postAbs

end Framework
end AbsInterpLTS
