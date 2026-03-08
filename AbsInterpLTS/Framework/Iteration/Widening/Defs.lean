import Cslib.Init

namespace AbsInterpLTS
namespace Framework
namespace Iteration

universe u

/-- Widening interface for abstract iterative solvers. -/
abbrev Widen (Abstract : Type u) := Abstract -> Abstract -> Abstract

end Iteration
end Framework
end AbsInterpLTS
