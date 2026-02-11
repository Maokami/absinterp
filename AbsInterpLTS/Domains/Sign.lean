import Cslib.Init

namespace AbsInterpLTS
namespace Domains

/-- Placeholder sign domain interface. Detailed semantics are added in staged issues. -/
inductive Sign where
  | bot
  | neg
  | zero
  | pos
  | top
  deriving DecidableEq, Repr

/-- Concretization hook for sign domain (bootstrap version). -/
def gammaSign : Sign -> Set Int
  | .bot => ∅
  | _ => Set.univ

end Domains
end AbsInterpLTS
