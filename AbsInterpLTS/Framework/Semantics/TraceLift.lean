import Cslib.Init

namespace AbsInterpLTS
namespace Framework

universe u v

/-!
# Generic Trace Lifting

`liftTrace` converts step-indexed transformers to trace-indexed transformers
by left-to-right composition over a label list.

For `compose : T -> T -> T`, identity `id : T`, and `step : Label -> T`:
`liftTrace compose id step labels = List.foldl (fun acc label => compose acc (step label)) id labels`.
-/

/--
Generic step-to-trace lifting by left-to-right composition over label lists.
-/
def liftTrace
    {Label : Type u}
    {T : Type v}
    (compose : T -> T -> T)
    (id : T)
    (step : Label -> T) :
    List Label -> T :=
  fun labels =>
    List.foldl
      (fun current label => compose current (step label))
      id
      labels

end Framework
end AbsInterpLTS
