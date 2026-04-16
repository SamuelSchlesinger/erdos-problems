/- 
# Explicit Seeds for Almost-Sidon Sets

The reflected-Sidon construction becomes completely explicit when we feed it a
concrete Sidon family. Reusing the geometric seed `1, 4, 4², ..., 4^m`, we get
an almost-Sidon subset of `{1, ..., N}` of size exactly `2(m + 1)` whenever
`4^m ≤ ⌊N/3⌋`.
-/
import Erdos.AlmostSidonSets.Construction
import Erdos.MaximalSidonSets.ExplicitSeeds

namespace AlmostSidonSets

open MaximalSidonSets

/-- If `4^m ≤ ⌊N/3⌋`, then reflecting the geometric seed
`{1, 4, 4², ..., 4^m}` across `N` produces an explicit almost-Sidon subset of
`{1, ..., N}` of size exactly `2(m + 1)`. -/
theorem doubledPowFourPrefix_almostSidonInInterval {m N : ℕ}
    (hN : 4 ^ m ≤ N / 3) :
    AlmostSidonInInterval (doubledFinset N (powFourPrefix m)) N ∧
      (doubledFinset N (powFourPrefix m)).card = 2 * (m + 1) := by
  have hSeed : MaximalSidonSets.SidonInInterval (powFourPrefix m) (N / 3) :=
    powFourPrefix_sidonInInterval hN
  have hSidon : IsSidonFinset (powFourPrefix m) := by
    simpa [AlmostSidonSets.IsSidonFinset, MaximalSidonSets.IsSidonFinset] using hSeed.1
  have hGround : ∀ b ∈ powFourPrefix m, b ∈ ground (N / 3) := by
    intro b hb
    simpa [AlmostSidonSets.ground, MaximalSidonSets.ground] using hSeed.2 b hb
  rcases doubledFinset_almostSidonInInterval hSidon hGround with ⟨hAlmost, hcard⟩
  refine ⟨hAlmost, ?_⟩
  simpa [powFourPrefix_card] using hcard

end AlmostSidonSets
