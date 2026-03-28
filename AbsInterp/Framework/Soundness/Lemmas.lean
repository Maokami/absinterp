import Cslib.Init

import AbsInterp.Framework.Soundness.Defs

namespace AbsInterp
namespace Framework

universe u v

/--
Composition closure for soundness.

If
- `post1` is sound w.r.t. `postSharp1`,
- `post2` is sound w.r.t. `postSharp2`, and
- `post2` is monotone,

then their sequential composition is sound:
`Sound (composePost post1 post2) gamma (composePostSharp postSharp1 postSharp2)`.
-/
theorem Sound.compose
    {State : Type u}
    {Abstract : Type v}
    {post1 post2 : Post State}
    {gamma : Gamma Abstract State}
    {postSharp1 postSharp2 : PostSharp Abstract}
    (h1 : Sound post1 gamma postSharp1)
    (h2 : Sound post2 gamma postSharp2)
    (hMono2 : MonotonePost post2) :
    Sound
      (composePost post1 post2)
      gamma
      (composePostSharp postSharp1 postSharp2) := by
  intro a s hs
  have hMono :
      post2 (post1 (gamma a)) ⊆ post2 (gamma (postSharp1 a)) :=
    hMono2 (h1 a)
  have hs' : s ∈ post2 (gamma (postSharp1 a)) := hMono hs
  exact h2 (postSharp1 a) hs'

end Framework
end AbsInterp
