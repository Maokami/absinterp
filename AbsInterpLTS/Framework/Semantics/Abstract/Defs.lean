import Cslib.Init

import AbsInterpLTS.Framework.Semantics.TraceLift

namespace AbsInterpLTS
namespace Framework

universe u v

/-!
# Abstract Semantic Transformers

This file mirrors `Concrete/Defs` at the abstract level, but keeps the core
interface order-agnostic.

For `stepPostSharp : Label -> (Abstract -> Abstract)`,
`liftTracePostSharp stepPostSharp` composes abstract step transformers left-to-right
along a label list.
-/

section Basic

/-- Abstract semantic transformer on abstract states. -/
abbrev PostSharp (Abstract : Type u) := Abstract -> Abstract

/-- Label-indexed one-step abstract transformers. -/
abbrev StepPostSharp (Abstract : Type u) (Label : Type v) := Label -> PostSharp Abstract

/-- Trace-indexed abstract transformers. -/
abbrev TracePostSharp (Abstract : Type u) (Label : Type v) := List Label -> PostSharp Abstract

/-- Sequential composition of abstract transformers. -/
def composePostSharp
    {Abstract : Type u}
    (postSharp1 postSharp2 : PostSharp Abstract) :
    PostSharp Abstract :=
  fun a => postSharp2 (postSharp1 a)

end Basic

section Trace

/--
Lift one-step abstract transfers to trace transfers by left-to-right composition.
-/
def liftTracePostSharp
    {Abstract : Type u}
    {Label : Type v}
    (stepPostSharp : StepPostSharp Abstract Label) :
    TracePostSharp Abstract Label :=
  liftTrace composePostSharp (fun a => a) stepPostSharp

end Trace

end Framework
end AbsInterpLTS
