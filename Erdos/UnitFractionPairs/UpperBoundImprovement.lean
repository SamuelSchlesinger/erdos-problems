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
  padicValNat 2 m % 3 ≠ 1 ∧ ¬ Even (padicValNat 3 m)

instance (m : ℕ) : Decidable (NewParam m) := by unfold NewParam; infer_instance

/-! ### Intra-disjointness of `{6m, 30m}` pairs for `m` coprime to 5. -/

/-- For distinct `m₁, m₂` both **coprime to 5**, the pairs `{6m₁, 30m₁}`
and `{6m₂, 30m₂}` are disjoint.

The four cases:
- `6m₁ = 6m₂ ⟹ m₁ = m₂` (contra `m₁ ≠ m₂`).
- `30m₁ = 30m₂ ⟹ m₁ = m₂`.
- `6m₁ = 30m₂ ⟹ m₁ = 5m₂`. But then `5 ∣ m₁`, contradicting `coprime m₁ 5`.
- `30m₁ = 6m₂ ⟹ m₂ = 5m₁`. Similarly `5 ∣ m₂`, contradicting `coprime m₂ 5`. -/
theorem new_pairs_disjoint_coprime5 {m₁ m₂ : ℕ} (hne : m₁ ≠ m₂)
    (h1 : Nat.Coprime m₁ 5) (h2 : Nat.Coprime m₂ 5) :
    Disjoint ({6 * m₁, 30 * m₁} : Finset ℕ) {6 * m₂, 30 * m₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
  -- 6m₁ = 6m₂
  · exact hne (by omega)
  -- 6m₁ = 30m₂ ⟹ m₁ = 5m₂, so 5 ∣ m₁, contradicting coprime m₁ 5.
  · have hm₁_eq : m₁ = 5 * m₂ := by omega
    have h5 : (5 : ℕ) ∣ m₁ := ⟨m₂, hm₁_eq⟩
    have hgcd : Nat.gcd m₁ 5 = 5 := Nat.gcd_eq_right h5
    rw [Nat.Coprime] at h1
    omega
  -- 30m₁ = 6m₂ ⟹ m₂ = 5m₁, so 5 ∣ m₂.
  · have hm₂_eq : m₂ = 5 * m₁ := by omega
    have h5 : (5 : ℕ) ∣ m₂ := ⟨m₁, hm₂_eq⟩
    have hgcd : Nat.gcd m₂ 5 = 5 := Nat.gcd_eq_right h5
    rw [Nat.Coprime] at h2
    omega
  -- 30m₁ = 30m₂
  · exact hne (by omega)

/-! ### Cross-disjointness with `S`-family `{3a, 6a}`.

For any `m` with `NewParam m` (so `v₃(m)` is odd), no element of
`{6m, 30m}` lies in any `{3a, 6a}` with `VDParam a` (which requires
`v₃(a)` even).

The argument: setting `6m = 3a` gives `a = 2m`, but `v₃(2m) = v₃(m)`
is odd, contradicting `VDParam`. Similarly for the other 3 cases —
all reduce to the same `v₃` parity mismatch. -/

/-- For nonzero `k, m` with `k` coprime to 3, `v₃(k·m) = v₃(m)`. -/
private lemma v3_mul_of_coprime3 {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    (hcop : ¬ (3 : ℕ) ∣ k) : padicValNat 3 (k * m) = padicValNat 3 m := by
  rw [padicValNat.mul hk hm]
  rw [padicValNat.eq_zero_of_not_dvd hcop, Nat.zero_add]

/-- **Cross-disjointness with the `S`-family.** For `m, a` both positive,
if `NewParam m` (so `v₃(m)` is odd) and `VDParam a` (so `v₃(a)` is even),
then `{6m, 30m} ∩ {3a, 6a} = ∅`. -/
theorem new_S_disjoint {m a : ℕ} (hm : 0 < m) (ha : 0 < a)
    (hNew : NewParam m) (hVD : VDParam a) :
    Disjoint ({6 * m, 30 * m} : Finset ℕ) {3 * a, 6 * a} := by
  obtain ⟨_, hm3⟩ := hNew  -- v₃(m) odd
  obtain ⟨_, ha3⟩ := hVD   -- v₃(a) even
  -- Show v₃(m) parity ≠ v₃(a) parity.
  rw [Finset.disjoint_left]
  intro x hx_new hx_S
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx_new hx_S
  -- Each of 4 cases gives a = c·m for some c, yielding v₃(a) = v₃(c) + v₃(m).
  -- v₃(a) even, v₃(m) odd, so v₃(c) odd. But c ∈ {2, 1, 10, 5}, all with v₃ = 0 even.
  -- Contradiction.
  -- Case 6m = 3a: a = 2m. v₃(a) = v₃(2m) = v₃(m). Even = odd, contra.
  -- Case 6m = 6a: a = m. v₃(a) = v₃(m). Even = odd, contra.
  -- Case 30m = 3a: a = 10m. v₃(a) = v₃(10m) = v₃(m). Contra.
  -- Case 30m = 6a: a = 5m. v₃(a) = v₃(5m) = v₃(m). Contra.
  rcases hx_new with rfl | rfl <;> rcases hx_S with h | h
  · -- 6m = 3a ⟹ a = 2m. v₃(a) = v₃(2m) = v₃(m), parity mismatch.
    have ha_eq : a = 2 * m := by omega
    rw [ha_eq, v3_mul_of_coprime3 (by norm_num : (2 : ℕ) ≠ 0)
      (by omega : m ≠ 0) (by norm_num : ¬ (3 : ℕ) ∣ 2)] at ha3
    exact hm3 ha3
  · -- 6m = 6a ⟹ a = m.
    have ha_eq : a = m := by omega
    rw [ha_eq] at ha3
    exact hm3 ha3
  · -- 30m = 3a ⟹ a = 10m.
    have ha_eq : a = 10 * m := by omega
    rw [ha_eq, v3_mul_of_coprime3 (by norm_num : (10 : ℕ) ≠ 0)
      (by omega : m ≠ 0) (by norm_num : ¬ (3 : ℕ) ∣ 10)] at ha3
    exact hm3 ha3
  · -- 30m = 6a ⟹ a = 5m.
    have ha_eq : a = 5 * m := by omega
    rw [ha_eq, v3_mul_of_coprime3 (by norm_num : (5 : ℕ) ≠ 0)
      (by omega : m ≠ 0) (by norm_num : ¬ (3 : ℕ) ∣ 5)] at ha3
    exact hm3 ha3

/-! ### Cross-disjointness with `T`-family `{4a, 12a}`.

Similar argument: setting `6m = 4a` ⟹ `a = 3m/2` requires `2 ∣ m`,
giving `a = 3·(m/2)`. Then `v₃(a) = 1 + v₃(m/2)`. For VDParam, `v₃(a)`
even, so `v₃(m/2)` odd. But NewParam needs `v₃(m)` odd, and (since `m`
even has `v₃(m) = v₃(m/2)`), `v₃(m/2)` odd → consistent. So just v₃
parity doesn't kill T case immediately.

The full argument uses the `v₂ mod 3` constraint too. Details omitted
here — the key insight is that the T-pair vertices have signature
`(2, 0)` and `(2, 1)`, while our pair vertices have signature in
`{(0, 0), (1, 0)}`. The `v₂ mod 3` mismatch forces disjointness. -/

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
