import Cslib.Init

namespace AbsInterpLTS
namespace Domains

/-- Placeholder interval domain interface. Detailed semantics are added in staged issues. -/
inductive Interval where
  | bot
  | range (lo hi : Int)
  | top
  deriving DecidableEq, Repr

/-- Concretization hook for interval domain (bootstrap version). -/
def gammaInterval : Interval -> Set Int
  | .bot => ∅
  | _ => Set.univ

end Domains
end AbsInterpLTS
