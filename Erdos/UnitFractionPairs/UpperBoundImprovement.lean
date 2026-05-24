/-
# Towards an Upper Bound Improvement Past 25/28 for #327

Van Doorn's `25/28 N` upper bound (`VanDoorn.lean`) uses two disjoint
pair families:

* `S_a = {3a, 6a}` with `1/(3a) + 1/(6a) = 1/(2a)` (forces 1 omission)
* `T_a = {4a, 12a}` with `1/(4a) + 1/(12a) = 1/(3a)` (forces 1 omission)

for `a` satisfying `VDParam` (`3 ∣ v₂(a)` and `Even v₃(a)`, density 3/7).
Total forced exclusion: `(3/7) · (1/6 + 1/12) = 1/14 + 1/28 = 3/28`.
Hence `f(N) ≤ N - 3N/28 = 25N/28`.

The natural question: can we find a **third** disjoint pair family,
pushing the bound below 25/28?

**The (1, 5)-shape new family `U_m = {6m, 30m}`** with `1/(6m) + 1/(30m)
= 1/(5m)`. To be disjoint from `S` and `T`, we need both `6m` and `30m`
to have *valuation signature* (`v₂ mod 3`, `v₃ mod 2`) outside the
S∪T-covered cells `{(0,1), (1,1), (2,0), (2,1)}`.

Since `6m` and `30m` share the same signature `(1 + v₂(m), 1 + v₃(m))`
mod `(3, 2)`, both being in the uncovered cells `{(0,0), (1,0)}`
requires

* `v₃(m)` odd (so `1 + v₃(m)` is even — matches "0" in second coord),
* `v₂(m) ≢ 1 (mod 3)` (so `1 + v₂(m) ≢ 2 (mod 3)`).

We call this `NewParam m`. Density of `NewParam`: `(4/7 + 1/7) · (1/4)
= 5/28`.

For intra-disjointness of `(6m, 30m)` pairs: need `m ≠ 5m'` for distinct
valid `m, m'`. Restricting to `m` coprime to 5 suffices. Density becomes
`5/28 · 4/5 = 1/7`.

Each pair forces 1 omission. `# pairs ≈ N / (30 · 7) = N / 210` for
`30m ≤ N`. So `U` contributes `1/210 ≈ 0.00476` to forced exclusion.

**New bound (after S, T, U):** `f(N) ≤ N · (1 - 3/28 - 1/210) =
N · (373/420) ≈ 0.8881 N`.

Improvement from `25/28 ≈ 0.8929` to `373/420 ≈ 0.8881` — a small
(≈ 0.5%) but real improvement. Combined with other shapes (e.g.,
(1,4)-shape `{5m, 20m}` for `v₂(m) ≡ 1 mod 3, v₃(m) even`), one can
push slightly further. This file lays the foundation; full
formalization of the bound is a larger undertaking.
-/

import Erdos.UnitFractionPairs.Classification
import Erdos.UnitFractionPairs.VanDoorn

namespace UnitFractionPairs

/-! ### The new pair shape `(6m, 30m)`. -/

/-- `(6m, 30m)` is a unit fraction pair for all `m`. The identity is
`1/(6m) + 1/(30m) = (5 + 1)/(30m) = 1/(5m)`. -/
theorem pair_6m_30m (m : ℕ) : IsUnitFractionPair (6 * m) (30 * m) :=
  ⟨5 * m, by ring⟩

/-- A pair-free set cannot contain both `6m` and `30m`. -/
theorem pair_free_not_6m_30m {A : Finset ℕ} (hA : PairFree A) {m : ℕ}
    (hm : 0 < m) (h6 : 6 * m ∈ A) (h30 : 30 * m ∈ A) : False :=
  hA (6 * m) h6 (30 * m) h30 (by omega) (pair_6m_30m m)

/-! ### Parameter predicate `NewParam`.

`NewParam m` ↔ `v₃(m)` is odd AND `v₂(m) ≢ 1 (mod 3)`. Equivalent to
"both `6m` and `30m` have signature outside the van Doorn S∪T cells". -/

/-- The valuation predicate for the new family: `v₂(m) ≢ 1 (mod 3)` and
`v₃(m)` is odd. -/
def NewParam (m : ℕ) : Prop :=
  m.factorization 2 % 3 ≠ 1 ∧ ¬ Even (m.factorization 3)

instance (m : ℕ) : Decidable (NewParam m) := by unfold NewParam; infer_instance

/-! ### Cardinality bound (sketch).

For `m` with `NewParam m` and `Nat.Coprime m 5`, the pair `(6m, 30m)` is
disjoint from any `(6m', 30m')` with `m' ≠ m` also satisfying the same
conditions, and is disjoint from every S- and T-pair.

The density of `NewParam ∩ coprime-to-5` is `(5/28) · (4/5) = 1/7`, giving
`N / 210` disjoint pairs for `30m ≤ N`, hence `≥ N/210` forced exclusions
beyond what S, T already capture.

The full formalization combining this with `vd_two_family_bound`
(`VanDoorn.lean`) requires:

1. **`pairs_disjoint_new_family`**: `(6m₁, 30m₁) ∩ (6m₂, 30m₂) = ∅` for
   distinct `m₁, m₂` both satisfying `NewParam ∧ coprime-to-5`.
2. **`pairs_cross_disjoint_S_T_new`**: `(6m, 30m) ∩ (S-pair) = ∅` and
   `(6m, 30m) ∩ (T-pair) = ∅` for all valid `m`.
3. **Three-family packing lemma**: extends `vd_two_family_bound` to handle
   the three pair families simultaneously.

These are sizeable but mechanical proofs paralleling the existing
`VanDoorn.lean` structure. -/

end UnitFractionPairs
