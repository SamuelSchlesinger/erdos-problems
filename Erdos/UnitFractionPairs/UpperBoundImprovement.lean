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
import Erdos.UnitFractionPairs.PairGadgets
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

For any of the 4 cases `6m = 4a`, `6m = 12a`, `30m = 4a`, `30m = 12a`,
we must have `2 ∣ m`. Write `m = 2k`; then `a = ck` for some `c ∈ {3, 1,
15, 5}`, all coprime to 2. Hence `v₂(a) = v₂(k)`, and `VDParam` requires
`3 ∣ v₂(a) = v₂(k)`, i.e., `v₂(k) ≡ 0 (mod 3)`.

But `v₂(m) = v₂(2k) = 1 + v₂(k)`, and `NewParam m` requires `v₂(m) ≢ 1
(mod 3)`. Combined: `v₂(k) ≢ 0 (mod 3)`. Contradiction. -/

/-- For nonzero `k, m` with `k` coprime to 2, `v₂(k·m) = v₂(m)`. -/
private lemma v2_mul_of_coprime2 {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    (hcop : ¬ (2 : ℕ) ∣ k) : padicValNat 2 (k * m) = padicValNat 2 m := by
  rw [padicValNat.mul hk hm]
  rw [padicValNat.eq_zero_of_not_dvd hcop, Nat.zero_add]

/-- For nonzero `m`, `v₂(2m) = 1 + v₂(m)`. -/
private lemma v2_two_mul (m : ℕ) (hm : m ≠ 0) :
    padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
  rw [padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) hm]
  rw [padicValNat.self (by norm_num : 1 < 2)]

/-- **Cross-disjointness with the `T`-family.** For `m, a` both positive,
if `NewParam m` (so `v₂(m) ≢ 1 (mod 3)`) and `VDParam a` (so `3 ∣ v₂(a)`),
then `{6m, 30m} ∩ {4a, 12a} = ∅`. -/
theorem new_T_disjoint {m a : ℕ} (hm : 0 < m) (ha : 0 < a)
    (hNew : NewParam m) (hVD : VDParam a) :
    Disjoint ({6 * m, 30 * m} : Finset ℕ) {4 * a, 12 * a} := by
  obtain ⟨hm2, _⟩ := hNew  -- v₂(m) mod 3 ≠ 1
  obtain ⟨ha2, _⟩ := hVD   -- 3 ∣ v₂(a)
  rw [Finset.disjoint_left]
  intro x hx_new hx_T
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx_new hx_T
  -- Each case: derive `2 ∣ m`, set `m = 2k`, derive `a = c·k` for `c` coprime to 2,
  -- giving `v₂(a) = v₂(k)`. Then `3 ∣ v₂(k)`, hence `v₂(m) = 1 + v₂(k) ≡ 1 (mod 3)`,
  -- contradicting `NewParam`.
  rcases hx_new with rfl | rfl <;> rcases hx_T with h | h
  · -- 6m = 4a ⟹ 3m = 2a ⟹ 2 | 3m ⟹ 2 | m. m = 2k, a = 3k.
    have h2m : 2 ∣ m := by
      have : 2 ∣ 3 * m := ⟨a, by omega⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 2 3 by decide) this)
    obtain ⟨k, rfl⟩ := h2m
    have hk_pos : 0 < k := by omega
    have ha_eq : a = 3 * k := by omega
    rw [ha_eq, v2_mul_of_coprime2 (k := 3) (m := k) (by norm_num) (by omega)
      (by norm_num : ¬ (2 : ℕ) ∣ 3)] at ha2
    -- v₂(m) = v₂(2k) = 1 + v₂(k). NewParam: v₂(m) ≢ 1 mod 3. So v₂(k) ≢ 0 mod 3.
    rw [v2_two_mul k (by omega)] at hm2
    -- 3 ∣ v₂(k) means v₂(k) = 0 mod 3. So 1 + v₂(k) ≡ 1 mod 3.
    omega
  · -- 6m = 12a ⟹ m = 2a.
    have h2m : 2 ∣ m := ⟨a, by omega⟩
    obtain ⟨k, rfl⟩ := h2m
    have ha_eq : a = k := by omega
    rw [ha_eq] at ha2
    rw [v2_two_mul k (by omega)] at hm2
    omega
  · -- 30m = 4a ⟹ 15m = 2a ⟹ 2 | 15m ⟹ 2 | m. m = 2k, a = 15k.
    have h2m : 2 ∣ m := by
      have : 2 ∣ 15 * m := ⟨a, by omega⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 2 15 by decide) this)
    obtain ⟨k, rfl⟩ := h2m
    have ha_eq : a = 15 * k := by omega
    rw [ha_eq, v2_mul_of_coprime2 (k := 15) (m := k) (by norm_num) (by omega)
      (by norm_num : ¬ (2 : ℕ) ∣ 15)] at ha2
    rw [v2_two_mul k (by omega)] at hm2
    omega
  · -- 30m = 12a ⟹ 5m = 2a ⟹ 2 | 5m ⟹ 2 | m. m = 2k, a = 5k.
    have h2m : 2 ∣ m := by
      have : 2 ∣ 5 * m := ⟨a, by omega⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 2 5 by decide) this)
    obtain ⟨k, rfl⟩ := h2m
    have ha_eq : a = 5 * k := by omega
    rw [ha_eq, v2_mul_of_coprime2 (k := 5) (m := k) (by norm_num) (by omega)
      (by norm_num : ¬ (2 : ℕ) ∣ 5)] at ha2
    rw [v2_two_mul k (by omega)] at hm2
    omega

/-! ### Three-family packing bound.

The S/T/U-pair helpers below are thin wrappers around the generic
`pair_card_eq_two`, `pair_subset_Icc`, and `pair_inter_card_le_one_of_pair`
from `Erdos/UnitFractionPairs/PairGadgets.lean`. -/

private theorem s_pair_card_eq_two {a : ℕ} (ha : 0 < a) :
    ({3 * a, 6 * a} : Finset ℕ).card = 2 := pair_card_eq_two (by omega)

private theorem t_pair_card_eq_two {a : ℕ} (ha : 0 < a) :
    ({4 * a, 12 * a} : Finset ℕ).card = 2 := pair_card_eq_two (by omega)

private theorem s_pair_subset_Icc {a N : ℕ} (ha : 0 < a) (h6 : 6 * a ≤ N) :
    ({3 * a, 6 * a} : Finset ℕ) ⊆ Finset.Icc 1 N :=
  pair_subset_Icc (by omega) (by omega) (by omega) (by omega)

private theorem t_pair_subset_Icc {a N : ℕ} (ha : 0 < a) (h12 : 12 * a ≤ N) :
    ({4 * a, 12 * a} : Finset ℕ) ⊆ Finset.Icc 1 N :=
  pair_subset_Icc (by omega) (by omega) (by omega) (by omega)

private theorem s_pair_inter_card_le_one {A : Finset ℕ} (hA : PairFree A)
    {a : ℕ} (ha : 0 < a) :
    (({3 * a, 6 * a} : Finset ℕ) ∩ A).card ≤ 1 :=
  pair_inter_card_le_one_of_pair hA (pair_3m_6m a) (by omega)

private theorem t_pair_inter_card_le_one {A : Finset ℕ} (hA : PairFree A)
    {a : ℕ} (ha : 0 < a) :
    (({4 * a, 12 * a} : Finset ℕ) ∩ A).card ≤ 1 :=
  pair_inter_card_le_one_of_pair hA (pair_4m_12m a) (by omega)

private theorem u_pair_card_eq_two {m : ℕ} (hm : 0 < m) :
    ({6 * m, 30 * m} : Finset ℕ).card = 2 := pair_card_eq_two (by omega)

private theorem u_pair_subset_Icc {m N : ℕ} (hm : 0 < m) (h30 : 30 * m ≤ N) :
    ({6 * m, 30 * m} : Finset ℕ) ⊆ Finset.Icc 1 N :=
  pair_subset_Icc (by omega) (by omega) (by omega) (by omega)

private theorem u_pair_inter_card_le_one {A : Finset ℕ} (hA : PairFree A)
    {m : ℕ} (hm : 0 < m) :
    (({6 * m, 30 * m} : Finset ℕ) ∩ A).card ≤ 1 :=
  pair_inter_card_le_one_of_pair hA (pair_6m_30m m) (by omega)

/-- **Three-family upper bound**: for every pair-free `A ⊆ [1, N]`,

  `|A| + |D_S| + |D_T| + |D_U| ≤ N`,

where:
- `D_S = {a ∈ [1, N/6] : VDParam a}` (van Doorn S-family parameters)
- `D_T = {a ∈ [1, N/12] : VDParam a}` (van Doorn T-family parameters)
- `D_U = {m ∈ [1, N/30] : NewParam m ∧ Coprime m 5}` (new U-family parameters)

Each `|D_X|` is `Θ(N)` (with proportionality from the density of the
parameter predicate). By the density calculations, `|D_S| ≈ N/14`,
`|D_T| ≈ N/28`, `|D_U| ≈ N/210`, giving the asymptotic bound

  `f(N) ≤ N · (1 - 1/14 - 1/28 - 1/210) = N · 373/420 ≈ 0.8881 N`,

a small but real improvement over van Doorn's `25/28 ≈ 0.8929`. -/
theorem three_family_pair_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card
           + ((Finset.Icc 1 (N / 12)).filter VDParam).card
           + ((Finset.Icc 1 (N / 30)).filter
               (fun m => NewParam m ∧ Nat.Coprime m 5)).card ≤ N := by
  set D_S := (Finset.Icc 1 (N / 6)).filter VDParam with hDS_def
  set D_T := (Finset.Icc 1 (N / 12)).filter VDParam with hDT_def
  set D_U := (Finset.Icc 1 (N / 30)).filter (fun m => NewParam m ∧ Nat.Coprime m 5)
    with hDU_def
  let s_pair : ℕ → Finset ℕ := fun a => {3*a, 6*a}
  let t_pair : ℕ → Finset ℕ := fun a => {4*a, 12*a}
  let u_pair : ℕ → Finset ℕ := fun m => {6*m, 30*m}
  -- Member properties
  have hDS_mem : ∀ a ∈ D_S, 0 < a ∧ VDParam a ∧ 6 * a ≤ N := by
    intro a ha; simp only [hDS_def, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have hDT_mem : ∀ a ∈ D_T, 0 < a ∧ VDParam a ∧ 12 * a ≤ N := by
    intro a ha; simp only [hDT_def, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have hDU_mem : ∀ m ∈ D_U, 0 < m ∧ NewParam m ∧ Nat.Coprime m 5 ∧ 30 * m ≤ N := by
    intro m hm; simp only [hDU_def, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨by omega, hm.2.1, hm.2.2, by omega⟩
  -- Apply three_family_bound
  have h := PackingBound.three_family_bound N A D_S D_T D_U s_pair t_pair u_pair
    2 1 2 1 2 1
    (by omega) (by omega) (by omega) hAN
    -- S-family pairwise disjoint
    (fun a₁ ha₁ a₂ ha₂ hne =>
      vd_s_pairs_disjoint (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).1
        (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).1 hne
        (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
        (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).2.1)
    -- S-family cardinality
    (fun a ha => s_pair_card_eq_two (hDS_mem a ha).1)
    -- S-family intersection bound
    (fun a ha => s_pair_inter_card_le_one hA (hDS_mem a ha).1)
    -- S-family ⊆ Icc
    (Finset.biUnion_subset.mpr fun a ha =>
      s_pair_subset_Icc (hDS_mem a ha).1 (hDS_mem a ha).2.2)
    -- T-family pairwise disjoint
    (fun a₁ ha₁ a₂ ha₂ hne =>
      vd_t_pairs_disjoint (hDT_mem a₁ (Finset.mem_coe.mp ha₁)).1
        (hDT_mem a₂ (Finset.mem_coe.mp ha₂)).1 hne
        (hDT_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
        (hDT_mem a₂ (Finset.mem_coe.mp ha₂)).2.1)
    -- T-family cardinality
    (fun a ha => t_pair_card_eq_two (hDT_mem a ha).1)
    -- T-family intersection bound
    (fun a ha => t_pair_inter_card_le_one hA (hDT_mem a ha).1)
    -- T-family ⊆ Icc
    (Finset.biUnion_subset.mpr fun a ha =>
      t_pair_subset_Icc (hDT_mem a ha).1 (hDT_mem a ha).2.2)
    -- U-family pairwise disjoint (uses new_pairs_disjoint_coprime5)
    (fun m₁ hm₁ m₂ hm₂ hne =>
      new_pairs_disjoint_coprime5 hne
        (hDU_mem m₁ (Finset.mem_coe.mp hm₁)).2.2.1
        (hDU_mem m₂ (Finset.mem_coe.mp hm₂)).2.2.1)
    -- U-family cardinality
    (fun m hm => u_pair_card_eq_two (hDU_mem m hm).1)
    -- U-family intersection bound
    (fun m hm => u_pair_inter_card_le_one hA (hDU_mem m hm).1)
    -- U-family ⊆ Icc
    (Finset.biUnion_subset.mpr fun m hm =>
      u_pair_subset_Icc (hDU_mem m hm).1 (hDU_mem m hm).2.2.2)
    -- S vs T cross-disjointness
    (by
      rw [Finset.disjoint_biUnion_left]
      intro a₁ ha₁; rw [Finset.disjoint_biUnion_right]; intro a₂ ha₂
      exact vd_s_t_cross_disjoint (hDS_mem a₁ ha₁).1 (hDT_mem a₂ ha₂).1
        (hDS_mem a₁ ha₁).2.1 (hDT_mem a₂ ha₂).2.1)
    -- S vs U cross-disjointness (uses new_S_disjoint, swapped)
    (by
      rw [Finset.disjoint_biUnion_left]
      intro a ha; rw [Finset.disjoint_biUnion_right]; intro m hm
      -- new_S_disjoint gives U disjoint with S; we need S with U.
      exact (new_S_disjoint (hDU_mem m hm).1 (hDS_mem a ha).1
        (hDU_mem m hm).2.1 (hDS_mem a ha).2.1).symm)
    -- T vs U cross-disjointness (uses new_T_disjoint, swapped)
    (by
      rw [Finset.disjoint_biUnion_left]
      intro a ha; rw [Finset.disjoint_biUnion_right]; intro m hm
      exact (new_T_disjoint (hDU_mem m hm).1 (hDT_mem a ha).1
        (hDU_mem m hm).2.1 (hDT_mem a ha).2.1).symm)
  -- three_family_bound gives A.card + |D_S| + |D_T| + |D_U| ≤ N
  omega

end UnitFractionPairs
