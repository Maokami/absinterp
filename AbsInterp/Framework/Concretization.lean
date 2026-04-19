import Mathlib.Data.Set.Defs

namespace AbsInterp
namespace Framework

universe u v

/-- Concretization map from abstract elements to sets of concrete values. -/
abbrev Concretization (Abstract : Type u) (Concrete : Type v) :=
  Abstract → Set Concrete

end Framework
end AbsInterp
