import Erdos.PermutationMonotoneAP.Statement
import Erdos.PermutationMonotoneAP.Dyadic
import Erdos.PermutationMonotoneAP.VanDerCorput
import Mathlib.Order.KonigLemma
import Mathlib.Data.Finset.Sort

/-!
# A compactness bridge for Erdős #196 (the 4-AP question)

We reduce #196 — *does ℕ admit a permutation with no monotone 4-term AP?* — to a
**finitary** statement: the existence of 4-AP-free orders of every initial segment
`[0,N)` under a single *uniform* displacement bound.

Think of an order on ℕ as a rank assignment `σ : ℕ → ℕ` (`σ v` = the position of value
`v`). The order is *type ω* exactly when every value has finitely many predecessors. A
*uniform* bound `σ v ≤ f v` guarantees this for free: `{u | σ u < σ v}` injects into
`{0,…,f v − 1}` (as `σ` is injective), so it is finite. Hence:

> **`FiniteFeasible f`** (4-AP-free injective orders of `[0,N)` with `σ v ≤ f v`, for all `N`)
> **⟹ `Erdos196Avoidable`** (a 4-AP-avoiding permutation of ℕ exists).

The proof threads the finite orders into a global `σ : ℕ → ℕ` by König's lemma
(`exists_seq_forall_proj_of_forall_finite`), then compresses `σ` to a genuine
permutation `ℕ ≃ ℕ` of order type ω, which inherits 4-AP-freeness.

Without the *uniform* `f`, compactness only yields a *dense* 4-AP-free order (e.g. van
der Corput); the uniform bound is exactly what forces order type ω. This is the precise
content of "the obstruction in #196 is purely the order type" — and it makes the problem
**construction-ready**: any uniform-bound finite construction (or an inductive existence
proof) yields #196 via this bridge.
-/

namespace PermutationMonotoneAP

open Function

/-- `σ : ℕ → ℕ` has a monotone 4-term AP below `N`: some AP `a, a+d, a+2d, a+3d`
(`d ≥ 1`, `a+3d < N`) whose `σ`-values are strictly monotone. -/
def HasMono4 (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + 3 * d < N ∧
    ((σ a < σ (a + d) ∧ σ (a + d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + 3 * d)) ∨
     (σ (a + 3 * d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + d) ∧ σ (a + d) < σ a))

/-- **Finite feasibility with uniform displacement bound `f`.** For every `N` there is
an injective rank assignment on `[0,N)` bounded by `f` and free of monotone 4-APs. -/
def FiniteFeasible (f : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ σ : ℕ → ℕ, Set.InjOn σ (Set.Iio N) ∧ (∀ v < N, σ v ≤ f v) ∧ ¬ HasMono4 σ N

/-- The concrete SAT-supported bound for the current #196 attack. -/
def twoMulAddSix (v : ℕ) : ℕ := 2 * v + 6

@[simp] theorem twoMulAddSix_apply (v : ℕ) : twoMulAddSix v = 2 * v + 6 := rfl

/-- `FiniteFeasible` is monotone in the pointwise bound. -/
theorem FiniteFeasible.mono {f g : ℕ → ℕ} (hfg : ∀ v, f v ≤ g v)
    (hf : FiniteFeasible f) : FiniteFeasible g := by
  intro N
  obtain ⟨σ, hinj, hbound, hfree⟩ := hf N
  exact ⟨σ, hinj, fun v hv => le_trans (hbound v hv) (hfg v), hfree⟩

/-- Every finite initial segment can be ordered to avoid monotone 4-APs, with no uniform
bound required. This is deliberately weaker than `FiniteFeasible`: it records that the
finite obstruction is not the issue in Erdős #196. -/
def FiniteOrderable4 : Prop :=
  ∀ N : ℕ, ∃ σ : ℕ → ℕ, Set.InjOn σ (Set.Iio N) ∧ ¬ HasMono4 σ N

/-- A single AP `a, a+d, a+2d, a+3d` is `σ`-monotone (strictly increasing or strictly
decreasing). -/
def Mono4 (σ : ℕ → ℕ) (a d : ℕ) : Prop :=
  (σ a < σ (a + d) ∧ σ (a + d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + 3 * d)) ∨
  (σ (a + 3 * d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + d) ∧ σ (a + d) < σ a)

theorem hasMono4_iff (σ : ℕ → ℕ) (N : ℕ) :
    HasMono4 σ N ↔ ∃ a d : ℕ, 0 < d ∧ a + 3 * d < N ∧ Mono4 σ a d := Iff.rfl

/-! ### Parity-merge decomposition

The construction-side attack on #196 is naturally dyadic. If `σ` is the rank assignment
for a finite order, its even and odd residue-class children are obtained by rescaling
`2i` and `2i+1`. Every even-difference 4-AP lives entirely in one child; only
odd-difference APs see the merge between the two streams. Thus a parity-merge
construction only has to prove three things: the even child is safe, the odd child is
safe, and the merge kills all odd-difference APs.
-/

/-- The order induced by `σ` on the even residue class, rescaled by `/2`. -/
def evenChild (σ : ℕ → ℕ) (i : ℕ) : ℕ := σ (2 * i)

/-- The order induced by `σ` on the odd residue class, rescaled by `/2`. -/
def oddChild (σ : ℕ → ℕ) (i : ℕ) : ℕ := σ (2 * i + 1)

/-- An even-difference AP starting at an even value is monotone for `σ` exactly when
the rescaled AP is monotone in the even child. -/
theorem mono4_evenChild_iff (σ : ℕ → ℕ) (b q : ℕ) :
    Mono4 (evenChild σ) b q ↔ Mono4 σ (2 * b) (2 * q) := by
  unfold Mono4 evenChild
  ring_nf

/-- An even-difference AP starting at an odd value is monotone for `σ` exactly when
the rescaled AP is monotone in the odd child. -/
theorem mono4_oddChild_iff (σ : ℕ → ℕ) (b q : ℕ) :
    Mono4 (oddChild σ) b q ↔ Mono4 σ (2 * b + 1) (2 * q) := by
  unfold Mono4 oddChild
  ring_nf

/-- The order induced by `σ` on a general dyadic residue class, rescaled by `2^j`.
The parity children are the special cases `j = 1, c = 0` and `j = 1, c = 1`. -/
def dyadicChild (j c : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ := σ (c + 2 ^ j * i)

/-- A 4-AP in a rescaled dyadic child is the same monotonicity statement as the
corresponding 4-AP in the parent with common difference multiplied by `2^j`. -/
theorem mono4_dyadicChild_iff (σ : ℕ → ℕ) (j c b q : ℕ) :
    Mono4 (dyadicChild j c σ) b q ↔ Mono4 σ (c + 2 ^ j * b) (2 ^ j * q) := by
  unfold Mono4 dyadicChild
  ring_nf

/-- The odd-difference safety condition for a finite merged order: every AP with odd
common difference is non-monotone. This is the merge-specific obligation in the dyadic
construction program. -/
def OddDiffSafe (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → d % 2 = 1 → a + 3 * d < N → ¬ Mono4 σ a d

/-- An edge-break certificate for odd-difference APs. For every odd-difference 4-AP,
one adjacent edge breaks the increasing pattern and one adjacent edge breaks the
decreasing pattern. This is the shape seen in the SAT witnesses: most APs are nearly
monotone, but a local inversion prevents an actual monotone 4-run. -/
def OddDiffEdgeBreakSafe (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → d % 2 = 1 → a + 3 * d < N →
    ((σ (a + d) ≤ σ a) ∨
      (σ (a + 2 * d) ≤ σ (a + d)) ∨
      (σ (a + 3 * d) ≤ σ (a + 2 * d))) ∧
    ((σ (a + 2 * d) ≤ σ (a + 3 * d)) ∨
      (σ (a + d) ≤ σ (a + 2 * d)) ∨
      (σ a ≤ σ (a + d)))

/-- Edge-break certificates imply the concise `OddDiffSafe` condition. -/
theorem OddDiffEdgeBreakSafe.oddDiffSafe {σ : ℕ → ℕ} {N : ℕ}
    (h : OddDiffEdgeBreakSafe σ N) : OddDiffSafe σ N := by
  intro a d hd hdodd hN
  obtain ⟨hinc, hdec⟩ := h a d hd hdodd hN
  rintro (⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩)
  · rcases hinc with hbreak | hbreak | hbreak
    · exact (not_lt.mpr hbreak) h01
    · exact (not_lt.mpr hbreak) h12
    · exact (not_lt.mpr hbreak) h23
  · rcases hdec with hbreak | hbreak | hbreak
    · exact (not_lt.mpr hbreak) h32
    · exact (not_lt.mpr hbreak) h21
    · exact (not_lt.mpr hbreak) h10

/-- Conversely, `OddDiffSafe` gives the explicit adjacent-edge-break certificate for
each odd-difference AP. The edge-break predicate is therefore just a proof-friendly
normal form, not a strengthening. -/
theorem OddDiffSafe.edgeBreakSafe {σ : ℕ → ℕ} {N : ℕ}
    (h : OddDiffSafe σ N) : OddDiffEdgeBreakSafe σ N := by
  intro a d hd hdodd hN
  have hnot := h a d hd hdodd hN
  constructor
  · by_cases h01 : σ a < σ (a + d)
    · by_cases h12 : σ (a + d) < σ (a + 2 * d)
      · by_cases h23 : σ (a + 2 * d) < σ (a + 3 * d)
        · exact False.elim (hnot (Or.inl ⟨h01, h12, h23⟩))
        · exact Or.inr (Or.inr (not_lt.mp h23))
      · exact Or.inr (Or.inl (not_lt.mp h12))
    · exact Or.inl (not_lt.mp h01)
  · by_cases h32 : σ (a + 3 * d) < σ (a + 2 * d)
    · by_cases h21 : σ (a + 2 * d) < σ (a + d)
      · by_cases h10 : σ (a + d) < σ a
        · exact False.elim (hnot (Or.inr ⟨h32, h21, h10⟩))
        · exact Or.inr (Or.inr (not_lt.mp h10))
      · exact Or.inr (Or.inl (not_lt.mp h21))
    · exact Or.inl (not_lt.mp h32)

/-- Odd-difference safety is equivalent to the adjacent-edge-break normal form. -/
theorem oddDiffEdgeBreakSafe_iff {σ : ℕ → ℕ} {N : ℕ} :
    OddDiffEdgeBreakSafe σ N ↔ OddDiffSafe σ N :=
  ⟨OddDiffEdgeBreakSafe.oddDiffSafe, OddDiffSafe.edgeBreakSafe⟩

/-- If every even value precedes every odd value, then every odd-difference 4-AP
alternates low/high/low/high (or high/low/high/low), so it cannot be monotone. This is
the basic local merge mechanism behind the dyadic construction attempts. -/
theorem OddDiffSafe.of_even_before_odd {σ : ℕ → ℕ} {N : ℕ}
    (hEO : ∀ x y : ℕ, x % 2 = 0 → y % 2 = 1 → σ x < σ y) :
    OddDiffSafe σ N := by
  intro a d _hd hdodd _hN
  rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
  · have p : (a + d) % 2 = 1 ∧ (a + 2 * d) % 2 = 0 ∧
        (a + 3 * d) % 2 = 1 := by omega
    have h21 : σ (a + 2 * d) < σ (a + d) := hEO _ _ p.2.1 p.1
    have h23 : σ (a + 2 * d) < σ (a + 3 * d) := hEO _ _ p.2.1 p.2.2
    rintro (⟨_, h12, _⟩ | ⟨h32, _, _⟩)
    · exact (not_lt.mpr h21.le) h12
    · exact (not_lt.mpr h23.le) h32
  · have p : (a + d) % 2 = 0 ∧ (a + 2 * d) % 2 = 1 ∧
        (a + 3 * d) % 2 = 0 := by omega
    have h10 : σ (a + d) < σ a := hEO _ _ p.1 ha1
    have h12 : σ (a + d) < σ (a + 2 * d) := hEO _ _ p.1 p.2.1
    rintro (⟨h01, _, _⟩ | ⟨_, h21, _⟩)
    · exact (not_lt.mpr h10.le) h01
    · exact (not_lt.mpr h12.le) h21

/-- Local finite version of `OddDiffSafe.of_even_before_odd`: it is enough for evens
below `N` to precede odds below `N`, since every AP counted by `OddDiffSafe σ N` lies
inside `[0,N)`. -/
theorem OddDiffSafe.of_even_before_odd_below {σ : ℕ → ℕ} {N : ℕ}
    (hEO : ∀ x y : ℕ, x < N → y < N → x % 2 = 0 → y % 2 = 1 → σ x < σ y) :
    OddDiffSafe σ N := by
  intro a d hd hdodd hN
  rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
  · have p : (a + d) % 2 = 1 ∧ (a + 2 * d) % 2 = 0 ∧
        (a + 3 * d) % 2 = 1 := by omega
    have h21 : σ (a + 2 * d) < σ (a + d) := hEO _ _ (by omega) (by omega) p.2.1 p.1
    have h23 : σ (a + 2 * d) < σ (a + 3 * d) := hEO _ _ (by omega) (by omega) p.2.1 p.2.2
    rintro (⟨_, h12, _⟩ | ⟨h32, _, _⟩)
    · exact (not_lt.mpr h21.le) h12
    · exact (not_lt.mpr h23.le) h32
  · have p : (a + d) % 2 = 0 ∧ (a + 2 * d) % 2 = 1 ∧
        (a + 3 * d) % 2 = 0 := by omega
    have h10 : σ (a + d) < σ a := hEO _ _ (by omega) (by omega) p.1 ha1
    have h12 : σ (a + d) < σ (a + 2 * d) := hEO _ _ (by omega) (by omega) p.1 p.2.1
    rintro (⟨h01, _, _⟩ | ⟨_, h21, _⟩)
    · exact (not_lt.mpr h10.le) h01
    · exact (not_lt.mpr h12.le) h21

/-- The symmetric local merge certificate: putting every odd value before every even
value also kills all odd-difference 4-APs. -/
theorem OddDiffSafe.of_odd_before_even {σ : ℕ → ℕ} {N : ℕ}
    (hOE : ∀ x y : ℕ, x % 2 = 1 → y % 2 = 0 → σ x < σ y) :
    OddDiffSafe σ N := by
  intro a d _hd hdodd _hN
  rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
  · have p : (a + d) % 2 = 1 ∧ (a + 2 * d) % 2 = 0 ∧
        (a + 3 * d) % 2 = 1 := by omega
    have h10 : σ (a + d) < σ a := hOE _ _ p.1 ha0
    have h12 : σ (a + d) < σ (a + 2 * d) := hOE _ _ p.1 p.2.1
    rintro (⟨h01, _, _⟩ | ⟨_, h21, _⟩)
    · exact (not_lt.mpr h10.le) h01
    · exact (not_lt.mpr h12.le) h21
  · have p : (a + d) % 2 = 0 ∧ (a + 2 * d) % 2 = 1 ∧
        (a + 3 * d) % 2 = 0 := by omega
    have h21 : σ (a + 2 * d) < σ (a + d) := hOE _ _ p.2.1 p.1
    have h23 : σ (a + 2 * d) < σ (a + 3 * d) := hOE _ _ p.2.1 p.2.2
    rintro (⟨_, h12, _⟩ | ⟨h32, _, _⟩)
    · exact (not_lt.mpr h21.le) h12
    · exact (not_lt.mpr h23.le) h32

/-- Local finite version of `OddDiffSafe.of_odd_before_even`. -/
theorem OddDiffSafe.of_odd_before_even_below {σ : ℕ → ℕ} {N : ℕ}
    (hOE : ∀ x y : ℕ, x < N → y < N → x % 2 = 1 → y % 2 = 0 → σ x < σ y) :
    OddDiffSafe σ N := by
  intro a d hd hdodd hN
  rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
  · have p : (a + d) % 2 = 1 ∧ (a + 2 * d) % 2 = 0 ∧
        (a + 3 * d) % 2 = 1 := by omega
    have h10 : σ (a + d) < σ a := hOE _ _ (by omega) (by omega) p.1 ha0
    have h12 : σ (a + d) < σ (a + 2 * d) := hOE _ _ (by omega) (by omega) p.1 p.2.1
    rintro (⟨h01, _, _⟩ | ⟨_, h21, _⟩)
    · exact (not_lt.mpr h10.le) h01
    · exact (not_lt.mpr h12.le) h21
  · have p : (a + d) % 2 = 0 ∧ (a + 2 * d) % 2 = 1 ∧
        (a + 3 * d) % 2 = 0 := by omega
    have h21 : σ (a + 2 * d) < σ (a + d) := hOE _ _ (by omega) (by omega) p.2.1 p.1
    have h23 : σ (a + 2 * d) < σ (a + 3 * d) := hOE _ _ (by omega) (by omega) p.2.1 p.2.2
    rintro (⟨_, h12, _⟩ | ⟨h32, _, _⟩)
    · exact (not_lt.mpr h21.le) h12
    · exact (not_lt.mpr h23.le) h32

/-- **Parity-merge decomposition.** To prove that a finite order `σ` has no monotone
4-AP below `N`, it suffices to prove that even-difference APs are safe in both rescaled
children and odd-difference APs are killed by the merge. This isolates the live
construction burden for Erdős #196: build a bounded merge satisfying `OddDiffSafe`. -/
theorem not_hasMono4_of_parity_children
    {σ : ℕ → ℕ} {N : ℕ}
    (hEven : ∀ b q : ℕ, 0 < q → 2 * (b + 3 * q) < N → ¬ Mono4 (evenChild σ) b q)
    (hOdd : ∀ b q : ℕ, 0 < q → 2 * (b + 3 * q) + 1 < N → ¬ Mono4 (oddChild σ) b q)
    (hOddDiff : OddDiffSafe σ N) :
    ¬ HasMono4 σ N := by
  rintro ⟨a, d, hd, h3, hmono⟩
  rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hd0
    have hq : 0 < q := by omega
    rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
    · obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero ha0
      exact hEven b q hq (by omega) ((mono4_evenChild_iff σ b q).mpr hmono)
    · set b := a / 2 with hb
      have ha : a = 2 * b + 1 := by
        have h := (Nat.div_add_mod a 2).symm
        rw [ha1] at h
        simpa [hb, Nat.mul_comm] using h
      rw [ha] at h3 hmono
      exact hOdd b q hq (by omega) ((mono4_oddChild_iff σ b q).mpr hmono)
  · exact hOddDiff a d hd hd1 h3 hmono

/-- A more ergonomic parity-merge decomposition: if the rescaled even and odd children
avoid all monotone 4-APs in their natural finite ranges, and the merge kills
odd-difference APs, then the merged order avoids all monotone 4-APs below `N`. -/
theorem not_hasMono4_of_child_orders
    {σ : ℕ → ℕ} {N : ℕ}
    (hEven : ¬ HasMono4 (evenChild σ) ((N + 1) / 2))
    (hOdd : ¬ HasMono4 (oddChild σ) (N / 2))
    (hOddDiff : OddDiffSafe σ N) :
    ¬ HasMono4 σ N :=
  not_hasMono4_of_parity_children
    (fun b q hq hN hmono => hEven ⟨b, q, hq, by omega, hmono⟩)
    (fun b q hq hN hmono => hOdd ⟨b, q, hq, by omega, hmono⟩)
    hOddDiff

/-- Child-order decomposition using the edge-break form of the merge obligation. -/
theorem not_hasMono4_of_child_orders_edgeBreak
    {σ : ℕ → ℕ} {N : ℕ}
    (hEven : ¬ HasMono4 (evenChild σ) ((N + 1) / 2))
    (hOdd : ¬ HasMono4 (oddChild σ) (N / 2))
    (hOddDiff : OddDiffEdgeBreakSafe σ N) :
    ¬ HasMono4 σ N :=
  not_hasMono4_of_child_orders hEven hOdd hOddDiff.oddDiffSafe

/-- Conversely, 4-AP-freeness of the parent implies 4-AP-freeness of the even child. -/
theorem not_hasMono4_evenChild {σ : ℕ → ℕ} {N : ℕ} (h : ¬ HasMono4 σ N) :
    ¬ HasMono4 (evenChild σ) ((N + 1) / 2) := by
  rintro ⟨a, d, hd, hN, hmono⟩
  exact h ⟨2 * a, 2 * d, by omega, by omega, (mono4_evenChild_iff σ a d).mp hmono⟩

/-- Conversely, 4-AP-freeness of the parent implies 4-AP-freeness of the odd child. -/
theorem not_hasMono4_oddChild {σ : ℕ → ℕ} {N : ℕ} (h : ¬ HasMono4 σ N) :
    ¬ HasMono4 (oddChild σ) (N / 2) := by
  rintro ⟨a, d, hd, hN, hmono⟩
  exact h ⟨2 * a + 1, 2 * d, by omega, by omega, (mono4_oddChild_iff σ a d).mp hmono⟩

/-- Parent 4-AP-freeness immediately implies odd-difference safety. -/
theorem OddDiffSafe.of_not_hasMono4 {σ : ℕ → ℕ} {N : ℕ}
    (h : ¬ HasMono4 σ N) : OddDiffSafe σ N := by
  intro a d hd _hdodd hN hmono
  exact h ⟨a, d, hd, hN, hmono⟩

/-- If every strict comparison made by `σ` below `N` is compatible with the van der
Corput order, then `σ` has no odd-difference monotone 4-AP below `N`. This is a useful
bridge for stage-varying dyadic merges: it is enough to show that the local merge
comparisons refine `vdcLt` on the four AP terms. -/
theorem OddDiffSafe.of_vdcLt_order_below {σ : ℕ → ℕ} {N : ℕ}
    (hσ : ∀ {x y : ℕ}, x < N → y < N → σ x < σ y → VDC.vdcLt x y) :
    OddDiffSafe σ N := by
  intro a d hd _hdodd hN
  have ha : a < N := by omega
  have ha1 : a + d < N := by omega
  have ha2 : a + 2 * d < N := by omega
  have ha3 : a + 3 * d < N := by omega
  intro hmono
  apply VDC.vdc_no_monotone_fourAP a d hd
  rcases hmono with ⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩
  · exact Or.inl
      ⟨hσ ha ha1 h01, hσ ha1 ha2 h12, hσ ha2 ha3 h23⟩
  · exact Or.inr
      ⟨hσ ha3 ha2 h32, hσ ha2 ha1 h21, hσ ha1 ha h10⟩

/-- The two same-parity endpoint pairs of a 4-AP point in opposite rank directions.
For odd common difference, these are exactly the endpoint comparisons inside the even
and odd children. -/
def EndpointOrientationDisagree (σ : ℕ → ℕ) (a d : ℕ) : Prop :=
  (σ a < σ (a + 2 * d) ∧ σ (a + 3 * d) < σ (a + d)) ∨
  (σ (a + 2 * d) < σ a ∧ σ (a + d) < σ (a + 3 * d))

/-- A local zigzag on the three adjacent rank edges of a 4-AP. These are the strict
`+-+` and `-+-` patterns visible in the SAT witnesses. -/
def MergeZigzag (σ : ℕ → ℕ) (a d : ℕ) : Prop :=
  (σ a < σ (a + d) ∧ σ (a + 2 * d) < σ (a + d) ∧
    σ (a + 2 * d) < σ (a + 3 * d)) ∨
  (σ (a + d) < σ a ∧ σ (a + d) < σ (a + 2 * d) ∧
    σ (a + 3 * d) < σ (a + 2 * d))

/-- The proof-guided odd-AP invariant suggested by the numerics: every odd-difference
AP is killed either because the two child endpoint orientations disagree, or because
the parent merge creates a strict local zigzag. -/
def OddAPSplitSafe (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → d % 2 = 1 → a + 3 * d < N →
    EndpointOrientationDisagree σ a d ∨ MergeZigzag σ a d

/-- To prove `OddAPSplitSafe`, it suffices to handle the two normal forms for the
initial parity of the AP and write the odd common difference as `2q+1`. -/
theorem OddAPSplitSafe.of_parity_cases {σ : ℕ → ℕ} {N : ℕ}
    (hEvenStart : ∀ b q : ℕ, 2 * b + 3 * (2 * q + 1) < N →
      EndpointOrientationDisagree σ (2 * b) (2 * q + 1) ∨
        MergeZigzag σ (2 * b) (2 * q + 1))
    (hOddStart : ∀ b q : ℕ, 2 * b + 1 + 3 * (2 * q + 1) < N →
      EndpointOrientationDisagree σ (2 * b + 1) (2 * q + 1) ∨
        MergeZigzag σ (2 * b + 1) (2 * q + 1)) :
    OddAPSplitSafe σ N := by
  intro a d hd hdodd hN
  have hq : ∃ q : ℕ, d = 2 * q + 1 := by
    refine ⟨d / 2, ?_⟩
    have h := (Nat.div_add_mod d 2).symm
    rw [hdodd] at h
    simpa [Nat.mul_comm] using h
  obtain ⟨q, rfl⟩ := hq
  rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
  · obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero ha0
    exact hEvenStart b q (by omega)
  · set b := a / 2 with hb
    have ha : a = 2 * b + 1 := by
      have h := (Nat.div_add_mod a 2).symm
      rw [ha1] at h
      simpa [hb, Nat.mul_comm] using h
    rw [ha] at hN ⊢
    exact hOddStart b q (by omega)

/-- If the two same-parity endpoint pairs of a 4-AP point in opposite rank directions,
then the whole 4-AP cannot be monotone. This captures one of the two mechanisms visible
in the SAT witnesses: many odd-difference APs die before using the detailed merge word,
because the even child and odd child orient their endpoint pairs differently. -/
theorem not_mono4_of_endpoint_orientation_disagree {σ : ℕ → ℕ} {a d : ℕ}
    (hdis : EndpointOrientationDisagree σ a d) :
    ¬ Mono4 σ a d := by
  rcases hdis with ⟨h02, h31⟩ | ⟨h20, h13⟩
  · rintro (⟨_h01, h12, h23⟩ | ⟨_h32, h21, h10⟩)
    · exact (not_lt.mpr h31.le) (lt_trans h12 h23)
    · exact (not_lt.mpr h02.le) (lt_trans h21 h10)
  · rintro (⟨h01, h12, _h23⟩ | ⟨h32, h21, _h10⟩)
    · exact (not_lt.mpr h20.le) (lt_trans h01 h12)
    · exact (not_lt.mpr h13.le) (lt_trans h32 h21)

/-- Endpoint-disagreement for an odd-difference AP starting at an even value can be
checked entirely in the two child orders. -/
theorem endpointOrientationDisagree_even_start_of_child_orders
    {N : ℕ} {σe σo σ : ℕ → ℕ} {b q : ℕ}
    (hEvenOrd : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j))
    (hOddOrd : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j))
    (hN : 2 * b + 3 * (2 * q + 1) < N)
    (h :
      (σe b < σe (b + 2 * q + 1) ∧
        σo (b + 3 * q + 1) < σo (b + q)) ∨
      (σe (b + 2 * q + 1) < σe b ∧
        σo (b + q) < σo (b + 3 * q + 1))) :
    EndpointOrientationDisagree σ (2 * b) (2 * q + 1) := by
  have hbE : b < (N + 1) / 2 := by omega
  have hb2E : b + 2 * q + 1 < (N + 1) / 2 := by omega
  have hbqO : b + q < N / 2 := by omega
  have hb3O : b + 3 * q + 1 < N / 2 := by omega
  rcases h with ⟨he, ho⟩ | ⟨he, ho⟩
  · left
    constructor
    · have he' : σ (2 * b) < σ (2 * (b + 2 * q + 1)) :=
        (hEvenOrd b (b + 2 * q + 1) hbE hb2E).mpr he
      convert he' using 2
      all_goals ring_nf
    · have ho' : σ (2 * (b + 3 * q + 1) + 1) < σ (2 * (b + q) + 1) :=
        (hOddOrd (b + 3 * q + 1) (b + q) hb3O hbqO).mpr ho
      convert ho' using 2
      all_goals ring_nf
  · right
    constructor
    · have he' : σ (2 * (b + 2 * q + 1)) < σ (2 * b) :=
        (hEvenOrd (b + 2 * q + 1) b hb2E hbE).mpr he
      convert he' using 2
      all_goals ring_nf
    · have ho' : σ (2 * (b + q) + 1) < σ (2 * (b + 3 * q + 1) + 1) :=
        (hOddOrd (b + q) (b + 3 * q + 1) hbqO hb3O).mpr ho
      convert ho' using 2
      all_goals ring_nf

/-- Endpoint-disagreement for an odd-difference AP starting at an odd value can be
checked entirely in the two child orders. -/
theorem endpointOrientationDisagree_odd_start_of_child_orders
    {N : ℕ} {σe σo σ : ℕ → ℕ} {b q : ℕ}
    (hEvenOrd : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j))
    (hOddOrd : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j))
    (hN : 2 * b + 1 + 3 * (2 * q + 1) < N)
    (h :
      (σo b < σo (b + 2 * q + 1) ∧
        σe (b + 3 * q + 2) < σe (b + q + 1)) ∨
      (σo (b + 2 * q + 1) < σo b ∧
        σe (b + q + 1) < σe (b + 3 * q + 2))) :
    EndpointOrientationDisagree σ (2 * b + 1) (2 * q + 1) := by
  have hbO : b < N / 2 := by omega
  have hb2O : b + 2 * q + 1 < N / 2 := by omega
  have hbqE : b + q + 1 < (N + 1) / 2 := by omega
  have hb3E : b + 3 * q + 2 < (N + 1) / 2 := by omega
  rcases h with ⟨ho, he⟩ | ⟨ho, he⟩
  · left
    constructor
    · have ho' : σ (2 * b + 1) < σ (2 * (b + 2 * q + 1) + 1) :=
        (hOddOrd b (b + 2 * q + 1) hbO hb2O).mpr ho
      convert ho' using 2
      all_goals ring_nf
    · have he' : σ (2 * (b + 3 * q + 2)) < σ (2 * (b + q + 1)) :=
        (hEvenOrd (b + 3 * q + 2) (b + q + 1) hb3E hbqE).mpr he
      convert he' using 2
      all_goals ring_nf
  · right
    constructor
    · have ho' : σ (2 * (b + 2 * q + 1) + 1) < σ (2 * b + 1) :=
        (hOddOrd (b + 2 * q + 1) b hb2O hbO).mpr ho
      convert ho' using 2
      all_goals ring_nf
    · have he' : σ (2 * (b + q + 1)) < σ (2 * (b + 3 * q + 2)) :=
        (hEvenOrd (b + q + 1) (b + 3 * q + 2) hbqE hb3E).mpr he
      convert he' using 2
      all_goals ring_nf

/-- A strict local zigzag is incompatible with monotonicity of the 4-AP. -/
theorem not_mono4_of_mergeZigzag {σ : ℕ → ℕ} {a d : ℕ}
    (hzig : MergeZigzag σ a d) :
    ¬ Mono4 σ a d := by
  rcases hzig with ⟨h01, h21, h23⟩ | ⟨h10, h12, h32⟩
  · rintro (⟨_h01', h12, _h23'⟩ | ⟨h32, _h21', _h10'⟩)
    · exact (not_lt.mpr h21.le) h12
    · exact (not_lt.mpr h23.le) h32
  · rintro (⟨h01, _h12', _h23'⟩ | ⟨_h32', h21, _h10'⟩)
    · exact (not_lt.mpr h10.le) h01
    · exact (not_lt.mpr h12.le) h21

/-- The orientation-aware local repair condition for one odd-difference 4-AP. When
the same-parity endpoint pairs point in the same direction, it rules out exactly the
bad shuffles that would leave the AP monotone. This is weaker than separating the two
parity pairs and is the local condition suggested by the finite searches. -/
def EndpointAgreementZigzagRepair (σ : ℕ → ℕ) (a d : ℕ) : Prop :=
  ((σ a < σ (a + 2 * d) ∧ σ (a + d) < σ (a + 3 * d)) →
    σ (a + 2 * d) < σ (a + d) ∨
      (σ (a + d) < σ a ∧ σ (a + 3 * d) < σ (a + 2 * d))) ∧
  ((σ (a + 2 * d) < σ a ∧ σ (a + 3 * d) < σ (a + d)) →
    σ (a + d) < σ (a + 2 * d) ∨
      (σ a < σ (a + d) ∧ σ (a + 2 * d) < σ (a + 3 * d)))

/-- A rank assignment avoids the orientation-aware bad shuffles on every odd-difference
4-AP below `N`. Under injectivity this implies `OddAPSplitSafe`; the definition is
separated out because it is the local combinatorial condition a merge word should
satisfy. -/
def BadShuffleAvoiding (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → d % 2 = 1 → a + 3 * d < N →
    EndpointAgreementZigzagRepair σ a d

/-- Forward endpoint agreement plus the first repair alternative creates the `+-+`
merge zigzag. -/
theorem mergeZigzag_of_forward_endpoint_agreement_left {σ : ℕ → ℕ} {a d : ℕ}
    (hAC : σ a < σ (a + 2 * d))
    (hBD : σ (a + d) < σ (a + 3 * d))
    (hCB : σ (a + 2 * d) < σ (a + d)) :
    MergeZigzag σ a d := by
  left
  exact ⟨lt_trans hAC hCB, hCB, lt_trans hCB hBD⟩

/-- Forward endpoint agreement plus the second repair alternative creates the `-+-`
merge zigzag. -/
theorem mergeZigzag_of_forward_endpoint_agreement_right {σ : ℕ → ℕ} {a d : ℕ}
    (hAC : σ a < σ (a + 2 * d))
    (hBA : σ (a + d) < σ a)
    (hDC : σ (a + 3 * d) < σ (a + 2 * d)) :
    MergeZigzag σ a d := by
  right
  exact ⟨hBA, lt_trans hBA hAC, hDC⟩

/-- Backward endpoint agreement plus the first repair alternative creates the `-+-`
merge zigzag. -/
theorem mergeZigzag_of_backward_endpoint_agreement_left {σ : ℕ → ℕ} {a d : ℕ}
    (hCA : σ (a + 2 * d) < σ a)
    (hDB : σ (a + 3 * d) < σ (a + d))
    (hBC : σ (a + d) < σ (a + 2 * d)) :
    MergeZigzag σ a d := by
  right
  exact ⟨lt_trans hBC hCA, hBC, lt_trans hDB hBC⟩

/-- Backward endpoint agreement plus the second repair alternative creates the `+-+`
merge zigzag. -/
theorem mergeZigzag_of_backward_endpoint_agreement_right {σ : ℕ → ℕ} {a d : ℕ}
    (hDB : σ (a + 3 * d) < σ (a + d))
    (hAB : σ a < σ (a + d))
    (hCD : σ (a + 2 * d) < σ (a + 3 * d)) :
    MergeZigzag σ a d := by
  left
  exact ⟨hAB, lt_trans hCD hDB, hCD⟩

/-- If both same-parity endpoint pairs are distinct, the orientation-aware repair
condition is enough to prove the split invariant for this AP: opposite orientations
give `EndpointOrientationDisagree`, while same orientations are forced into a
`MergeZigzag`. -/
theorem endpointAgreementZigzagRepair_or_disagree {σ : ℕ → ℕ} {a d : ℕ}
    (hACne : σ a ≠ σ (a + 2 * d))
    (hBDne : σ (a + d) ≠ σ (a + 3 * d))
    (hrepair : EndpointAgreementZigzagRepair σ a d) :
    EndpointOrientationDisagree σ a d ∨ MergeZigzag σ a d := by
  rcases lt_or_gt_of_ne hACne with hAC | hCA
  · rcases lt_or_gt_of_ne hBDne with hBD | hDB
    · right
      rcases hrepair.1 ⟨hAC, hBD⟩ with hCB | ⟨hBA, hDC⟩
      · exact mergeZigzag_of_forward_endpoint_agreement_left hAC hBD hCB
      · exact mergeZigzag_of_forward_endpoint_agreement_right hAC hBA hDC
    · left
      exact Or.inl ⟨hAC, hDB⟩
  · rcases lt_or_gt_of_ne hBDne with hBD | hDB
    · left
      exact Or.inr ⟨hCA, hBD⟩
    · right
      rcases hrepair.2 ⟨hCA, hDB⟩ with hBC | ⟨hAB, hCD⟩
      · exact mergeZigzag_of_backward_endpoint_agreement_left hCA hDB hBC
      · exact mergeZigzag_of_backward_endpoint_agreement_right hDB hAB hCD

/-- The bad-shuffle formulation is strong enough to prove the split odd-AP invariant
for an injective finite rank assignment. -/
theorem OddAPSplitSafe.of_badShuffleAvoiding {σ : ℕ → ℕ} {N : ℕ}
    (hinj : Set.InjOn σ (Set.Iio N))
    (hbad : BadShuffleAvoiding σ N) :
    OddAPSplitSafe σ N := by
  intro a d hd hdodd hN
  have haN : a < N := lt_of_le_of_lt (Nat.le_add_right a (3 * d)) hN
  have hacN : a + 2 * d < N := by
    exact lt_of_le_of_lt (by omega : a + 2 * d ≤ a + 3 * d) hN
  have habN : a + d < N := by
    exact lt_of_le_of_lt (by omega : a + d ≤ a + 3 * d) hN
  have hACne : σ a ≠ σ (a + 2 * d) := by
    intro hEq
    have ha : a ∈ Set.Iio N := Set.mem_Iio.mpr haN
    have hc : a + 2 * d ∈ Set.Iio N := Set.mem_Iio.mpr hacN
    have hidx := hinj ha hc hEq
    omega
  have hBDne : σ (a + d) ≠ σ (a + 3 * d) := by
    intro hEq
    have hb : a + d ∈ Set.Iio N := Set.mem_Iio.mpr habN
    have hd' : a + 3 * d ∈ Set.Iio N := Set.mem_Iio.mpr hN
    have hidx := hinj hb hd' hEq
    omega
  exact endpointAgreementZigzagRepair_or_disagree hACne hBDne
    (hbad a d hd hdodd hN)

/-- Odd-difference safety follows if every odd-difference AP below `N` has opposite
orientations on its same-parity endpoint pairs. This isolates the "child orientation
disagreement" half of the observed construction pattern; the remaining APs must be
killed by local merge zigzags. -/
theorem OddDiffSafe.of_endpoint_orientation_disagree {σ : ℕ → ℕ} {N : ℕ}
    (h :
      ∀ a d : ℕ, 0 < d → d % 2 = 1 → a + 3 * d < N →
        (σ a < σ (a + 2 * d) ∧ σ (a + 3 * d) < σ (a + d)) ∨
        (σ (a + 2 * d) < σ a ∧ σ (a + d) < σ (a + 3 * d))) :
    OddDiffSafe σ N := by
  intro a d hd hdodd hN
  exact not_mono4_of_endpoint_orientation_disagree (h a d hd hdodd hN)

/-- The split odd-AP invariant implies ordinary odd-difference safety. -/
theorem OddDiffSafe.of_splitSafe {σ : ℕ → ℕ} {N : ℕ}
    (h : OddAPSplitSafe σ N) : OddDiffSafe σ N := by
  intro a d hd hdodd hN
  rcases h a d hd hdodd hN with hdis | hzig
  · exact not_mono4_of_endpoint_orientation_disagree hdis
  · exact not_mono4_of_mergeZigzag hzig

/-- The split odd-AP invariant also gives the edge-break normal form required by
`MergeWitness`. -/
theorem OddDiffEdgeBreakSafe.of_splitSafe {σ : ℕ → ℕ} {N : ℕ}
    (h : OddAPSplitSafe σ N) : OddDiffEdgeBreakSafe σ N :=
  (OddDiffSafe.of_splitSafe h).edgeBreakSafe

/-- One-step parity merge with all evens before odds: if both children are 4-AP-free
in their rescaled ranges and the finite merge puts every even below `N` before every
odd below `N`, then the merged finite order is 4-AP-free. This is the finite version of
the pure vdc merge step; it is too rigid for the final `ω` construction, but it is the
base certificate a relaxed merge has to generalize. -/
theorem not_hasMono4_of_child_orders_even_before_odd
    {σ : ℕ → ℕ} {N : ℕ}
    (hEven : ¬ HasMono4 (evenChild σ) ((N + 1) / 2))
    (hOdd : ¬ HasMono4 (oddChild σ) (N / 2))
    (hEO : ∀ x y : ℕ, x < N → y < N → x % 2 = 0 → y % 2 = 1 → σ x < σ y) :
    ¬ HasMono4 σ N :=
  not_hasMono4_of_child_orders hEven hOdd (OddDiffSafe.of_even_before_odd_below hEO)

/-- Symmetric one-step parity merge with all odds before evens. -/
theorem not_hasMono4_of_child_orders_odd_before_even
    {σ : ℕ → ℕ} {N : ℕ}
    (hEven : ¬ HasMono4 (evenChild σ) ((N + 1) / 2))
    (hOdd : ¬ HasMono4 (oddChild σ) (N / 2))
    (hOE : ∀ x y : ℕ, x < N → y < N → x % 2 = 1 → y % 2 = 0 → σ x < σ y) :
    ¬ HasMono4 σ N :=
  not_hasMono4_of_child_orders hEven hOdd (OddDiffSafe.of_odd_before_even_below hOE)

/-- Adding a constant to every rank preserves the `Mono4` predicate. -/
theorem mono4_add_const_iff (C : ℕ) (σ : ℕ → ℕ) (a d : ℕ) :
    Mono4 (fun i => C + σ i) a d ↔ Mono4 σ a d := by
  unfold Mono4
  constructor
  · rintro (⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩)
    · exact Or.inl
        ⟨Nat.add_lt_add_iff_left.mp h01,
         Nat.add_lt_add_iff_left.mp h12,
         Nat.add_lt_add_iff_left.mp h23⟩
    · exact Or.inr
        ⟨Nat.add_lt_add_iff_left.mp h32,
         Nat.add_lt_add_iff_left.mp h21,
         Nat.add_lt_add_iff_left.mp h10⟩
  · rintro (⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩)
    · exact Or.inl
        ⟨Nat.add_lt_add_iff_left.mpr h01,
         Nat.add_lt_add_iff_left.mpr h12,
         Nat.add_lt_add_iff_left.mpr h23⟩
    · exact Or.inr
        ⟨Nat.add_lt_add_iff_left.mpr h32,
         Nat.add_lt_add_iff_left.mpr h21,
         Nat.add_lt_add_iff_left.mpr h10⟩

/-- Adding a constant to every rank preserves 4-AP-freeness below `N`. -/
theorem not_hasMono4_add_const {C N : ℕ} {σ : ℕ → ℕ} (h : ¬ HasMono4 σ N) :
    ¬ HasMono4 (fun i => C + σ i) N := by
  rintro ⟨a, d, hd, hN, hmono⟩
  exact h ⟨a, d, hd, hN, (mono4_add_const_iff C σ a d).mp hmono⟩

/-- Rigid two-block parity merge: evens are ranked by `σe`; odds are ranked by `σo`
after a fixed offset `M`, so every sufficiently bounded even rank precedes every odd. -/
def parityBlockRank (M : ℕ) (σe σo : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v % 2 = 0 then σe (v / 2) else M + σo (v / 2)

/-- The even child of the rigid parity block merge is exactly the even input order. -/
theorem evenChild_parityBlockRank (M : ℕ) (σe σo : ℕ → ℕ) :
    evenChild (parityBlockRank M σe σo) = σe := by
  funext i
  unfold evenChild parityBlockRank
  rw [Nat.mul_mod_right]
  simp

/-- The odd child of the rigid parity block merge is the odd input order shifted by
the block offset. -/
theorem oddChild_parityBlockRank (M : ℕ) (σe σo : ℕ → ℕ) :
    oddChild (parityBlockRank M σe σo) = fun i => M + σo i := by
  funext i
  unfold oddChild parityBlockRank
  have hmod : (2 * i + 1) % 2 = 1 := by omega
  have hdiv : (2 * i + 1) / 2 = i := by omega
  rw [hmod, hdiv]
  simp

/-- Rigid parity-block merge constructor. If the even and odd child orders are free
in their natural ranges and all even ranks fit below the offset `M`, then placing the
whole even stream before the shifted odd stream gives a 4-AP-free finite order.

This recovers the finite vdc-style merge step. It is intentionally too rigid for the
final `ω` construction (small odd values are delayed by the offset); the next attack is
to weaken this to a bounded, stage-varying merge while retaining an `OddDiffSafe`
certificate. -/
theorem parityBlockRank_not_hasMono4 {M N : ℕ} {σe σo : ℕ → ℕ}
    (hEven : ¬ HasMono4 σe ((N + 1) / 2))
    (hOdd : ¬ HasMono4 σo (N / 2))
    (hEvenBound : ∀ i : ℕ, i < (N + 1) / 2 → σe i < M) :
    ¬ HasMono4 (parityBlockRank M σe σo) N := by
  apply not_hasMono4_of_child_orders_even_before_odd
  · rw [evenChild_parityBlockRank]
    exact hEven
  · rw [oddChild_parityBlockRank]
    exact not_hasMono4_add_const hOdd
  · intro x y hx _hy hx0 hy1
    unfold parityBlockRank
    have hxdiv : x / 2 < (N + 1) / 2 := by omega
    rw [hx0, hy1]
    exact Nat.lt_add_right _ (hEvenBound (x / 2) hxdiv)

/-- A finite rank assignment satisfying the exact parity-merge obligations: injective
and bounded on `[0,N)`, both rescaled children are 4-AP-free in their natural ranges,
and the merge has an odd-difference edge-break certificate. This is the construction
interface suggested by the SAT witnesses. -/
def MergeWitness (f : ℕ → ℕ) (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (Set.Iio N) ∧
  (∀ v < N, σ v ≤ f v) ∧
  ¬ HasMono4 (evenChild σ) ((N + 1) / 2) ∧
  ¬ HasMono4 (oddChild σ) (N / 2) ∧
  OddDiffEdgeBreakSafe σ N

/-- A prepared finite witness for the concrete `2v+6` construction program. Compared
with `MergeWitness`, this keeps the odd-difference proof in the more informative split
form seen in the numerics: each odd AP is killed by child endpoint disagreement or by a
strict local merge zigzag. This is the predicate whose recursive closure is now the main
proof target. -/
def GoodWitness (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (Set.Iio N) ∧
  (∀ v < N, σ v ≤ twoMulAddSix v) ∧
  ¬ HasMono4 (evenChild σ) ((N + 1) / 2) ∧
  ¬ HasMono4 (oddChild σ) (N / 2) ∧
  OddAPSplitSafe σ N

/-- The weaker finite witness actually needed for the compactness bridge: an injective
bounded finite order with no monotone 4-APs. Unlike `GoodWitness`, this does not ask
the witness to carry a recursively reusable odd-AP split certificate. -/
def ConcreteWitness (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (Set.Iio N) ∧
  (∀ v < N, σ v ≤ twoMulAddSix v) ∧
  ¬ HasMono4 σ N

/-- A concrete witness whose value `0` is first. The direct finite searches show that
this weaker anchored invariant survives cases where the split-certificate family does
not. -/
def AnchoredConcreteWitness (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  ConcreteWitness N σ ∧ σ 0 = 0

/-- Prepared witnesses are ordinary merge witnesses for the concrete bound. -/
theorem mergeWitness_of_goodWitness {N : ℕ} {σ : ℕ → ℕ}
    (h : GoodWitness N σ) :
    MergeWitness twoMulAddSix N σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    OddDiffEdgeBreakSafe.of_splitSafe h.2.2.2.2⟩

/-- Prepared witnesses are finite-feasibility witnesses for the concrete bound. -/
theorem finiteFeasible_witness_of_goodWitness {N : ℕ} {σ : ℕ → ℕ}
    (h : GoodWitness N σ) :
    Set.InjOn σ (Set.Iio N) ∧ (∀ v < N, σ v ≤ twoMulAddSix v) ∧ ¬ HasMono4 σ N :=
  ⟨h.1, h.2.1,
    not_hasMono4_of_child_orders_edgeBreak h.2.2.1 h.2.2.2.1
      (OddDiffEdgeBreakSafe.of_splitSafe h.2.2.2.2)⟩

/-- Prepared witnesses are concrete witnesses. -/
theorem concreteWitness_of_goodWitness {N : ℕ} {σ : ℕ → ℕ}
    (h : GoodWitness N σ) :
    ConcreteWitness N σ :=
  finiteFeasible_witness_of_goodWitness h

/-- A flexible one-step dyadic merge certificate. It says that the parent `σ` is
injective and bounded, preserves the internal strict order of both child witnesses, and
kills all odd-difference APs by an edge-break certificate. Unlike `parityBlockRank`,
this does not require one whole parity class to precede the other. -/
def DyadicMergeStep (f : ℕ → ℕ) (N : ℕ) (σe σo σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (Set.Iio N) ∧
  (∀ v < N, σ v ≤ f v) ∧
  (∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
    (σ (2 * i) < σ (2 * j) ↔ σe i < σe j)) ∧
  (∀ i j : ℕ, i < N / 2 → j < N / 2 →
    (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j)) ∧
  OddDiffEdgeBreakSafe σ N

/-! ### Lag budgets for balanced parity merges

The finite witnesses suggest that the parent order is obtained by interleaving the two
child orders with bounded prefix imbalance. The following definitions make the relevant
budget explicit without committing to a particular merge algorithm. For example,
`evenCompressedRankInParent σ N i` is the rank of `i` inside the even subsequence of the
parent order, while `EvenLagAtMost σ N C` says that the actual parent rank of `2i` is at
most `2` times this compressed rank, plus a merge-lag allowance `C`.
-/

/-- The finite compressed rank induced by an arbitrary finite rank assignment `τ` on
`[0,M)`: the number of earlier `τ`-values below `τ i`. This is the child-side analogue
of `evenCompressedRankInParent` and is the natural coordinate for a merge word. -/
def finiteCompressedRank (τ : ℕ → ℕ) (M i : ℕ) : ℕ :=
  ((Finset.range M).filter (fun j => τ j < τ i)).card

/-- Finite compressed rank is strictly monotone along the underlying finite order. -/
theorem finiteCompressedRank_lt_of_lt {τ : ℕ → ℕ} {M i j : ℕ}
    (hi : i < M) (hij : τ i < τ j) :
    finiteCompressedRank τ M i < finiteCompressedRank τ M j := by
  classical
  rw [finiteCompressedRank, finiteCompressedRank]
  apply Finset.card_lt_card
  have hsub : (Finset.range M).filter (fun u => τ u < τ i) ⊆
      (Finset.range M).filter (fun u => τ u < τ j) := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, lt_trans hu.2 hij⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hij⟩,
    fun hc => (lt_irrefl (τ i)) (Finset.mem_filter.mp hc).2⟩

/-- On an injective finite segment, comparing compressed ranks is the same as comparing
the original rank assignment. -/
theorem finiteCompressedRank_lt_iff {τ : ℕ → ℕ} {M i j : ℕ}
    (hinj : Set.InjOn τ (Set.Iio M)) (hi : i < M) (hj : j < M) :
    finiteCompressedRank τ M i < finiteCompressedRank τ M j ↔ τ i < τ j := by
  constructor
  · intro h
    by_contra hnot
    rcases lt_or_eq_of_le (not_lt.mp hnot) with hji | hji
    · exact (not_lt.mpr (finiteCompressedRank_lt_of_lt hj hji).le) h
    · have hidx : j = i := hinj (Set.mem_Iio.mpr hj) (Set.mem_Iio.mpr hi) hji
      subst hidx
      exact (lt_irrefl _) h
  · exact finiteCompressedRank_lt_of_lt hi

/-- Finite compressed rank is injective on the finite segment when the original rank
assignment is. -/
theorem finiteCompressedRank_injOn {τ : ℕ → ℕ} {M : ℕ}
    (hinj : Set.InjOn τ (Set.Iio M)) :
    Set.InjOn (finiteCompressedRank τ M) (Set.Iio M) := by
  intro i hi j hj h
  by_contra hne
  rcases lt_trichotomy (τ i) (τ j) with hij | hij | hij
  · have hrank := (finiteCompressedRank_lt_iff hinj (Set.mem_Iio.mp hi) (Set.mem_Iio.mp hj)).2 hij
    exact hrank.ne h
  · exact hne (hinj hi hj hij)
  · have hrank := (finiteCompressedRank_lt_iff hinj (Set.mem_Iio.mp hj) (Set.mem_Iio.mp hi)).2 hij
    exact hrank.ne h.symm

/-- The compressed rank of an element of `[0,M)` is itself below `M`. -/
theorem finiteCompressedRank_lt {τ : ℕ → ℕ} {M i : ℕ} (hi : i < M) :
    finiteCompressedRank τ M i < M := by
  classical
  have hlt : ((Finset.range M).filter (fun j => τ j < τ i)).card < (Finset.range M).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨i, Finset.mem_range.mpr hi,
      fun hc => (lt_irrefl (τ i)) (Finset.mem_filter.mp hc).2⟩
  simpa [finiteCompressedRank] using hlt

/-- The compressed rank is bounded by the original rank value on an injective finite
segment. This is often the first cheap source of child-rank credit. -/
theorem finiteCompressedRank_le_value {τ : ℕ → ℕ} {M i : ℕ}
    (hinj : Set.InjOn τ (Set.Iio M)) (_hi : i < M) :
    finiteCompressedRank τ M i ≤ τ i := by
  classical
  let s := (Finset.range M).filter (fun j => τ j < τ i)
  have hmaps : Set.MapsTo τ (↑s) (↑(Finset.range (τ i))) := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  have hinj' : Set.InjOn τ (↑s) := by
    intro x hx y hy hxy
    have hxlt : x < M := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < M := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    exact hinj (Set.mem_Iio.mpr hxlt) (Set.mem_Iio.mpr hylt) hxy
  have hcard := Finset.card_le_card_of_injOn τ hmaps hinj'
  simpa [finiteCompressedRank, s] using hcard

/-- The compressed rank of `i` inside the even subsequence of a parent rank assignment. -/
def evenCompressedRankInParent (σ : ℕ → ℕ) (N i : ℕ) : ℕ :=
  ((Finset.range ((N + 1) / 2)).filter (fun j => σ (2 * j) < σ (2 * i))).card

/-- The compressed rank of `i` inside the odd subsequence of a parent rank assignment. -/
def oddCompressedRankInParent (σ : ℕ → ℕ) (N i : ℕ) : ℕ :=
  ((Finset.range (N / 2)).filter (fun j => σ (2 * j + 1) < σ (2 * i + 1))).card

/-- If the parent preserves the even child order, then its even compressed ranks are
exactly the finite compressed ranks of the even child. -/
theorem evenCompressedRankInParent_eq_finiteCompressedRank_of_order {N : ℕ}
    {σe σ : ℕ → ℕ}
    (hord : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j)) :
    ∀ i : ℕ, i < (N + 1) / 2 →
      evenCompressedRankInParent σ N i =
        finiteCompressedRank σe ((N + 1) / 2) i := by
  intro i hi
  classical
  rw [evenCompressedRankInParent, finiteCompressedRank]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  exact hord j i (Finset.mem_range.mp hj) hi

/-- Odd analogue of `evenCompressedRankInParent_eq_finiteCompressedRank_of_order`. -/
theorem oddCompressedRankInParent_eq_finiteCompressedRank_of_order {N : ℕ}
    {σo σ : ℕ → ℕ}
    (hord : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j)) :
    ∀ i : ℕ, i < N / 2 →
      oddCompressedRankInParent σ N i =
        finiteCompressedRank σo (N / 2) i := by
  intro i hi
  classical
  rw [oddCompressedRankInParent, finiteCompressedRank]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  exact hord j i (Finset.mem_range.mp hj) hi

/-- Build a parent rank assignment by placing the `r`-th even child item in `evenSlot r`
and the `r`-th odd child item in `oddSlot r`, where child positions are first compressed
to `[0,M)`. This separates the merge word (`evenSlot`, `oddSlot`) from the internal
child orders (`σe`, `σo`). -/
def slotMergeRank (N : ℕ) (σe σo evenSlot oddSlot : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v % 2 = 0 then
    evenSlot (finiteCompressedRank σe ((N + 1) / 2) (v / 2))
  else
    oddSlot (finiteCompressedRank σo (N / 2) (v / 2))

@[simp] theorem slotMergeRank_even (N : ℕ) (σe σo evenSlot oddSlot : ℕ → ℕ)
    (i : ℕ) :
    slotMergeRank N σe σo evenSlot oddSlot (2 * i) =
      evenSlot (finiteCompressedRank σe ((N + 1) / 2) i) := by
  simp [slotMergeRank]

@[simp] theorem slotMergeRank_odd (N : ℕ) (σe σo evenSlot oddSlot : ℕ → ℕ)
    (i : ℕ) :
    slotMergeRank N σe σo evenSlot oddSlot (2 * i + 1) =
      oddSlot (finiteCompressedRank σo (N / 2) i) := by
  have hdiv : (2 * i + 1) / 2 = i := by omega
  simp [slotMergeRank, hdiv]

/-- If the even slots are strictly ordered by compressed rank, the slot-merge parent
preserves the even child's finite order. -/
theorem slotMergeRank_even_order {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenSlot r < evenSlot s ↔ r < s))
    (hinj : Set.InjOn σe (Set.Iio ((N + 1) / 2))) :
    ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (slotMergeRank N σe σo evenSlot oddSlot (2 * i) <
        slotMergeRank N σe σo evenSlot oddSlot (2 * j) ↔ σe i < σe j) := by
  intro i j hi hj
  rw [slotMergeRank_even, slotMergeRank_even]
  rw [hslot _ _ (finiteCompressedRank_lt hi) (finiteCompressedRank_lt hj)]
  exact finiteCompressedRank_lt_iff hinj hi hj

/-- Odd analogue of `slotMergeRank_even_order`. -/
theorem slotMergeRank_odd_order {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddSlot r < oddSlot s ↔ r < s))
    (hinj : Set.InjOn σo (Set.Iio (N / 2))) :
    ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (slotMergeRank N σe σo evenSlot oddSlot (2 * i + 1) <
        slotMergeRank N σe σo evenSlot oddSlot (2 * j + 1) ↔ σo i < σo j) := by
  intro i j hi hj
  rw [slotMergeRank_odd, slotMergeRank_odd]
  rw [hslot _ _ (finiteCompressedRank_lt hi) (finiteCompressedRank_lt hj)]
  exact finiteCompressedRank_lt_iff hinj hi hj

/-- In a slot merge whose even slots are ordered by compressed rank, the parent even
compressed rank is exactly the even child's compressed rank. -/
theorem evenCompressedRankInParent_slotMergeRank {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenSlot r < evenSlot s ↔ r < s))
    (hinj : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    {i : ℕ} (hi : i < (N + 1) / 2) :
    evenCompressedRankInParent (slotMergeRank N σe σo evenSlot oddSlot) N i =
      finiteCompressedRank σe ((N + 1) / 2) i := by
  classical
  rw [evenCompressedRankInParent, finiteCompressedRank]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  have hjlt : j < (N + 1) / 2 := Finset.mem_range.mp hj
  exact slotMergeRank_even_order hslot hinj j i hjlt hi

/-- Odd analogue of `evenCompressedRankInParent_slotMergeRank`. -/
theorem oddCompressedRankInParent_slotMergeRank {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddSlot r < oddSlot s ↔ r < s))
    (hinj : Set.InjOn σo (Set.Iio (N / 2)))
    {i : ℕ} (hi : i < N / 2) :
    oddCompressedRankInParent (slotMergeRank N σe σo evenSlot oddSlot) N i =
      finiteCompressedRank σo (N / 2) i := by
  classical
  rw [oddCompressedRankInParent, finiteCompressedRank]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  have hjlt : j < N / 2 := Finset.mem_range.mp hj
  exact slotMergeRank_odd_order hslot hinj j i hjlt hi

/-- A slot map whose strict comparisons exactly match the natural order is injective
on the finite slot range. -/
theorem slot_injOn_of_lt_iff_lt {M : ℕ} {slot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < M → s < M → (slot r < slot s ↔ r < s)) :
    Set.InjOn slot (Set.Iio M) := by
  intro r hr s hs hEq
  by_contra hne
  rcases lt_trichotomy r s with hrs | hrs | hsr
  · exact (hslot r s (Set.mem_Iio.mp hr) (Set.mem_Iio.mp hs)).2 hrs |>.ne hEq
  · exact hne hrs
  · exact (hslot s r (Set.mem_Iio.mp hs) (Set.mem_Iio.mp hr)).2 hsr |>.ne hEq.symm

/-- The slot-merge parent is injective below `N` when the two slot streams are
internally ordered and disjoint. -/
theorem slotMergeRank_injOn {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hinje : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    (hinjo : Set.InjOn σo (Set.Iio (N / 2)))
    (hslotE : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenSlot r < evenSlot s ↔ r < s))
    (hslotO : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddSlot r < oddSlot s ↔ r < s))
    (hdisj : ∀ r s : ℕ, r < (N + 1) / 2 → s < N / 2 →
      evenSlot r ≠ oddSlot s) :
    Set.InjOn (slotMergeRank N σe σo evenSlot oddSlot) (Set.Iio N) := by
  intro x hx y hy hxy
  have hxN : x < N := Set.mem_Iio.mp hx
  have hyN : y < N := Set.mem_Iio.mp hy
  have hinjE : Set.InjOn evenSlot (Set.Iio ((N + 1) / 2)) :=
    slot_injOn_of_lt_iff_lt hslotE
  have hinjO : Set.InjOn oddSlot (Set.Iio (N / 2)) :=
    slot_injOn_of_lt_iff_lt hslotO
  rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
  · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero hx0
    have hi : i < (N + 1) / 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one y with hy0 | hy1
    · obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero hy0
      have hj : j < (N + 1) / 2 := by omega
      have hslotEq :
          evenSlot (finiteCompressedRank σe ((N + 1) / 2) i) =
            evenSlot (finiteCompressedRank σe ((N + 1) / 2) j) := by
        simpa using hxy
      have hrankEq :
          finiteCompressedRank σe ((N + 1) / 2) i =
            finiteCompressedRank σe ((N + 1) / 2) j :=
        hinjE (Set.mem_Iio.mpr (finiteCompressedRank_lt hi))
          (Set.mem_Iio.mpr (finiteCompressedRank_lt hj)) hslotEq
      have hij : i = j :=
        finiteCompressedRank_injOn hinje (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj)
          hrankEq
      omega
    · set j := y / 2 with hjDef
      have hy_eq : y = 2 * j + 1 := by
        have h := (Nat.div_add_mod y 2).symm
        rw [hy1] at h
        simpa [hjDef, Nat.mul_comm] using h
      rw [hy_eq] at hyN hxy
      have hj : j < N / 2 := by omega
      exact False.elim
        (hdisj (finiteCompressedRank σe ((N + 1) / 2) i)
          (finiteCompressedRank σo (N / 2) j)
          (finiteCompressedRank_lt hi) (finiteCompressedRank_lt hj) (by simpa using hxy))
  · set i := x / 2 with hiDef
    have hx_eq : x = 2 * i + 1 := by
      have h := (Nat.div_add_mod x 2).symm
      rw [hx1] at h
      simpa [hiDef, Nat.mul_comm] using h
    rw [hx_eq] at hxN hxy
    have hi : i < N / 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one y with hy0 | hy1
    · obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero hy0
      have hj : j < (N + 1) / 2 := by omega
      exact False.elim
        (hdisj (finiteCompressedRank σe ((N + 1) / 2) j)
          (finiteCompressedRank σo (N / 2) i)
          (finiteCompressedRank_lt hj) (finiteCompressedRank_lt hi) (by simpa using hxy.symm))
    · set j := y / 2 with hjDef
      have hy_eq : y = 2 * j + 1 := by
        have h := (Nat.div_add_mod y 2).symm
        rw [hy1] at h
        simpa [hjDef, Nat.mul_comm] using h
      rw [hy_eq] at hyN hxy
      have hj : j < N / 2 := by omega
      have hslotEq :
          oddSlot (finiteCompressedRank σo (N / 2) i) =
            oddSlot (finiteCompressedRank σo (N / 2) j) := by
        simpa using hxy
      have hrankEq :
          finiteCompressedRank σo (N / 2) i =
            finiteCompressedRank σo (N / 2) j :=
        hinjO (Set.mem_Iio.mpr (finiteCompressedRank_lt hi))
          (Set.mem_Iio.mpr (finiteCompressedRank_lt hj)) hslotEq
      have hij : i = j :=
        finiteCompressedRank_injOn hinjo (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj)
          hrankEq
      omega

/-- Slot map induced by the increasing enumeration of a finite set of parent positions. -/
noncomputable def finSlot (N M : ℕ) (s : Finset (Fin N)) (hcard : s.card = M)
    (r : ℕ) : ℕ :=
  if hr : r < M then (s.orderEmbOfFin hcard ⟨r, hr⟩).val else 0

/-- `finSlot` is strictly ordered by its slot index on the finite range. -/
theorem finSlot_lt_iff {N M : ℕ} {s : Finset (Fin N)} {hcard : s.card = M}
    {r t : ℕ} (hr : r < M) (ht : t < M) :
    finSlot N M s hcard r < finSlot N M s hcard t ↔ r < t := by
  simp [finSlot, hr, ht,
    ((s.orderEmbOfFin hcard).lt_iff_lt (a := ⟨r, hr⟩) (b := ⟨t, ht⟩))]

/-- Disjoint finite position sets induce disjoint slot maps. -/
theorem finSlot_ne_of_disjoint {N Me Mo : ℕ} {s t : Finset (Fin N)}
    {hs : s.card = Me} {ht : t.card = Mo}
    (hd : Disjoint s t) {r u : ℕ} (hr : r < Me) (hu : u < Mo) :
    finSlot N Me s hs r ≠ finSlot N Mo t ht u := by
  intro hEq
  have hFin : s.orderEmbOfFin hs ⟨r, hr⟩ = t.orderEmbOfFin ht ⟨u, hu⟩ := by
    apply Fin.ext
    simpa [finSlot, hr, hu] using hEq
  have hsMem : s.orderEmbOfFin hs ⟨r, hr⟩ ∈ s := Finset.orderEmbOfFin_mem s hs ⟨r, hr⟩
  have htMem : s.orderEmbOfFin hs ⟨r, hr⟩ ∈ t := by
    rw [hFin]
    exact Finset.orderEmbOfFin_mem t ht ⟨u, hu⟩
  exact (Finset.disjoint_left.mp hd) hsMem htMem

/-- The slot map for the even stream, read from a finite set of even parent positions. -/
noncomputable def evenPositionSlot (N : ℕ) (E : Finset (Fin N))
    (hE : E.card = (N + 1) / 2) : ℕ → ℕ :=
  finSlot N ((N + 1) / 2) E hE

/-- The slot map for the odd stream, read from the complement of the even positions. -/
noncomputable def oddPositionSlot (N : ℕ) (E : Finset (Fin N))
    (hE : E.card = (N + 1) / 2) : ℕ → ℕ :=
  finSlot N (N / 2) Eᶜ (by
    classical
    rw [Finset.card_compl, hE]
    simp
    omega)

/-- Slot-level version of the exact even pointwise budget. -/
def EvenSlotPointwiseBudget (N : ℕ) (σe evenSlot : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, i < (N + 1) / 2 →
    (evenSlot (finiteCompressedRank σe ((N + 1) / 2) i) : ℤ) -
        2 * (finiteCompressedRank σe ((N + 1) / 2) i : ℤ) ≤
      2 * ((2 * i + 3 : ℕ) -
        (finiteCompressedRank σe ((N + 1) / 2) i : ℤ))

/-- Slot-level version of the exact odd pointwise budget. -/
def OddSlotPointwiseBudget (N : ℕ) (σo oddSlot : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, i < N / 2 →
    (oddSlot (finiteCompressedRank σo (N / 2) i) : ℤ) -
        (2 * (finiteCompressedRank σo (N / 2) i : ℤ) + 1) ≤
      2 * ((2 * i + 3 : ℕ) -
        (finiteCompressedRank σo (N / 2) i : ℤ)) + 1

/-- Scale-dependent slack for the deadline-aware invariant. It is stricter than `+6`
at small scales and becomes the old `+6` allowance once `log2 N ≥ 6`. -/
def scaleSlack (N : ℕ) : ℕ := min 6 (Nat.log2 N)

/-- The scale-tight deadline used by the current compatible-family attack. -/
def scaleBound (N v : ℕ) : ℕ := 2 * v + scaleSlack N

/-- A rank assignment respects the scale-tight deadlines on `[0,N)`. -/
def ScaleBounded (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  ∀ v : ℕ, v < N → σ v ≤ scaleBound N v

/-- Anchored scale-tight invariant: value `0` is first, and all values below `N`
respect the scale-tight deadlines. This is the first concrete compatible-family
candidate suggested by the small search: it removes the `N = 10` bad child pairs. -/
def AnchoredScaleBounded (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  ScaleBounded N σ ∧ σ 0 = 0

/-- Root-anchored witnesses: value `0` is first in the finite order. This weaker
invariant is the natural landing point after the scale-tight version proved too
restrictive for the recursive construction. -/
def Anchored (_N : ℕ) (σ : ℕ → ℕ) : Prop :=
  σ 0 = 0

/-- Scale-tight deadlines imply the concrete `2v+6` bound. -/
theorem scaleBound_le_twoMulAddSix (N v : ℕ) : scaleBound N v ≤ twoMulAddSix v := by
  have hslack : scaleSlack N ≤ 6 := by
    unfold scaleSlack
    exact min_le_left 6 (Nat.log2 N)
  unfold scaleBound twoMulAddSix
  omega

/-- Slot-level direct form of the scale-tight deadline. -/
def ScaleSlotBound (N : ℕ) (σe σo evenSlot oddSlot : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, i < (N + 1) / 2 →
    evenSlot (finiteCompressedRank σe ((N + 1) / 2) i) ≤ scaleBound N (2 * i)) ∧
  (∀ i : ℕ, i < N / 2 →
    oddSlot (finiteCompressedRank σo (N / 2) i) ≤ scaleBound N (2 * i + 1))

/-- Slot-level direct form of the concrete `2v+6` deadline. This is the construction
target once we stop forcing the auxiliary scale-tight bound. -/
def ConcreteSlotBound (N : ℕ) (σe σo evenSlot oddSlot : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, i < (N + 1) / 2 →
    evenSlot (finiteCompressedRank σe ((N + 1) / 2) i) ≤ twoMulAddSix (2 * i)) ∧
  (∀ i : ℕ, i < N / 2 →
    oddSlot (finiteCompressedRank σo (N / 2) i) ≤ twoMulAddSix (2 * i + 1))

/-- Direct even slot bounds imply the exact even pointwise budget. -/
theorem evenSlotPointwiseBudget_of_bound {N : ℕ} {σe evenSlot : ℕ → ℕ}
    (h : ∀ i : ℕ, i < (N + 1) / 2 →
      evenSlot (finiteCompressedRank σe ((N + 1) / 2) i) ≤ 2 * (2 * i) + 6) :
    EvenSlotPointwiseBudget N σe evenSlot := by
  intro i hi
  have hb := h i hi
  omega

/-- Direct odd slot bounds imply the exact odd pointwise budget. -/
theorem oddSlotPointwiseBudget_of_bound {N : ℕ} {σo oddSlot : ℕ → ℕ}
    (h : ∀ i : ℕ, i < N / 2 →
      oddSlot (finiteCompressedRank σo (N / 2) i) ≤ 2 * (2 * i + 1) + 6) :
    OddSlotPointwiseBudget N σo oddSlot := by
  intro i hi
  have hb := h i hi
  omega

/-- Concrete slot deadlines imply the exact even slot budget. -/
theorem evenSlotPointwiseBudget_of_concreteSlotBound {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (h : ConcreteSlotBound N σe σo evenSlot oddSlot) :
    EvenSlotPointwiseBudget N σe evenSlot :=
  evenSlotPointwiseBudget_of_bound (fun i hi => by
    simpa [twoMulAddSix] using h.1 i hi)

/-- Concrete slot deadlines imply the exact odd slot budget. -/
theorem oddSlotPointwiseBudget_of_concreteSlotBound {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (h : ConcreteSlotBound N σe σo evenSlot oddSlot) :
    OddSlotPointwiseBudget N σo oddSlot :=
  oddSlotPointwiseBudget_of_bound (fun i hi => by
    simpa [twoMulAddSix] using h.2 i hi)

/-- Scale slot bounds imply the exact slot budgets needed by `SlotMergeCompatible`. -/
theorem evenSlotPointwiseBudget_of_scaleSlotBound {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (h : ScaleSlotBound N σe σo evenSlot oddSlot) :
    EvenSlotPointwiseBudget N σe evenSlot :=
  evenSlotPointwiseBudget_of_bound (fun i hi =>
    (h.1 i hi).trans (scaleBound_le_twoMulAddSix N (2 * i)))

/-- Odd analogue of `evenSlotPointwiseBudget_of_scaleSlotBound`. -/
theorem oddSlotPointwiseBudget_of_scaleSlotBound {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (h : ScaleSlotBound N σe σo evenSlot oddSlot) :
    OddSlotPointwiseBudget N σo oddSlot :=
  oddSlotPointwiseBudget_of_bound (fun i hi =>
    (h.2 i hi).trans (scaleBound_le_twoMulAddSix N (2 * i + 1)))

/-- Scale slot bounds give the scale-tight parent invariant for the slot merge. -/
theorem scaleBounded_slotMergeRank_of_scaleSlotBound {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (h : ScaleSlotBound N σe σo evenSlot oddSlot) :
    ScaleBounded N (slotMergeRank N σe σo evenSlot oddSlot) := by
  intro v hv
  rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
  · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero hv0
    have hi : i < (N + 1) / 2 := by omega
    simpa [scaleBound] using h.1 i hi
  · set i := v / 2 with hiDef
    have hv_eq : v = 2 * i + 1 := by
      have hdiv := (Nat.div_add_mod v 2).symm
      rw [hv1] at hdiv
      simpa [hiDef, Nat.mul_comm] using hdiv
    rw [hv_eq] at hv ⊢
    have hi : i < N / 2 := by omega
    simpa [scaleBound] using h.2 i hi

/-- Slot condition that preserves the root anchor `σ 0 = 0`: if the even child is
anchored and the first even slot is parent position `0`, then the merged parent is
anchored at value `0`. -/
theorem slotMergeRank_zero_of_child_zero {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hσe0 : σe 0 = 0)
    (hslot0 : evenSlot 0 = 0) :
    slotMergeRank N σe σo evenSlot oddSlot 0 = 0 := by
  have hRank0 : finiteCompressedRank σe ((N + 1) / 2) 0 = 0 := by
    classical
    rw [finiteCompressedRank]
    apply Finset.card_eq_zero.mpr
    ext j
    simp [hσe0]
  simp [slotMergeRank, hRank0, hslot0]

/-- The root anchor is preserved by any merge whose first even slot is `0`. -/
theorem anchored_slotMergeRank_of_slot0 {N : ℕ} {σe σo evenSlot oddSlot : ℕ → ℕ}
    (he : Anchored ((N + 1) / 2) σe)
    (hslot0 : evenSlot 0 = 0) :
    Anchored N (slotMergeRank N σe σo evenSlot oddSlot) :=
  slotMergeRank_zero_of_child_zero he hslot0

/-- Scale slot bounds plus the root slot condition preserve the anchored scale-tight
invariant. -/
theorem anchoredScaleBounded_slotMergeRank_of_scaleSlotBound {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (he : AnchoredScaleBounded ((N + 1) / 2) σe)
    (hScale : ScaleSlotBound N σe σo evenSlot oddSlot)
    (hslot0 : evenSlot 0 = 0) :
    AnchoredScaleBounded N (slotMergeRank N σe σo evenSlot oddSlot) :=
  ⟨scaleBounded_slotMergeRank_of_scaleSlotBound hScale,
    slotMergeRank_zero_of_child_zero he.2 hslot0⟩

/-- Slot-level compatibility for merging two child witnesses at size `N`. This is the
new construction-facing target after the arbitrary-child merge proved too strong:
choose increasing, disjoint slots for the two child orders, meet the exact pointwise
deadlines, and prove the odd-AP split invariant for the resulting parent. -/
def SlotMergeCompatible (N : ℕ) (σe σo evenSlot oddSlot : ℕ → ℕ) : Prop :=
  (∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
    (evenSlot r < evenSlot s ↔ r < s)) ∧
  (∀ r s : ℕ, r < N / 2 → s < N / 2 →
    (oddSlot r < oddSlot s ↔ r < s)) ∧
  (∀ r s : ℕ, r < (N + 1) / 2 → s < N / 2 →
    evenSlot r ≠ oddSlot s) ∧
  EvenSlotPointwiseBudget N σe evenSlot ∧
  OddSlotPointwiseBudget N σo oddSlot ∧
  OddAPSplitSafe (slotMergeRank N σe σo evenSlot oddSlot) N

/-- A finite set of even parent positions gives the ordered/disjoint slot-map fields.
The remaining obligations are exactly the mathematical ones: deadlines and split-safety. -/
theorem slotMergeCompatible_of_evenPositionSet {N : ℕ} {σe σo : ℕ → ℕ}
    {E : Finset (Fin N)} (hE : E.card = (N + 1) / 2)
    (heBudget : EvenSlotPointwiseBudget N σe (evenPositionSlot N E hE))
    (hoBudget : OddSlotPointwiseBudget N σo (oddPositionSlot N E hE))
    (hSplit :
      OddAPSplitSafe
        (slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE)) N) :
    SlotMergeCompatible N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) := by
  classical
  refine ⟨?_, ?_, ?_, heBudget, hoBudget, hSplit⟩
  · intro r s hr hs
    exact finSlot_lt_iff hr hs
  · intro r s hr hs
    exact finSlot_lt_iff hr hs
  · intro r s hr hs
    exact finSlot_ne_of_disjoint (s := E) (t := Eᶜ)
      (hs := hE)
      (ht := by
        rw [Finset.card_compl, hE]
        simp
        omega)
      disjoint_compl_right hr hs

/-- A bound on even-child compressed ranks inside the parent. This is the recursive
child-rank budget seen in the SAT witnesses. -/
def EvenCompressedBound (A : ℕ) (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < (N + 1) / 2 → evenCompressedRankInParent σ N i ≤ 2 * i + A

/-- A bound on odd-child compressed ranks inside the parent. -/
def OddCompressedBound (A : ℕ) (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < N / 2 → oddCompressedRankInParent σ N i ≤ 2 * i + A

/-- If the parent preserves the even child's internal order, then the compressed even
rank of `i` inside the parent is at most the actual child rank `σe i`. This is the
basic bridge from child rank-credit bounds to the parent compressed-rank budget. -/
theorem evenCompressedRankInParent_le_child_rank {N : ℕ} {σe σ : ℕ → ℕ}
    (hinj : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    (hord : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j)) :
    ∀ i : ℕ, i < (N + 1) / 2 → evenCompressedRankInParent σ N i ≤ σe i := by
  intro i hi
  classical
  let s := (Finset.range ((N + 1) / 2)).filter (fun j => σ (2 * j) < σ (2 * i))
  have hmaps : Set.MapsTo σe (↑s) (↑(Finset.range (σe i))) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact Finset.mem_range.mpr ((hord j i (Finset.mem_range.mp hj'.1) hi).mp hj'.2)
  have hinj' : Set.InjOn σe (↑s) := by
    intro x hx y hy hxy
    have hxlt : x < (N + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < (N + 1) / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    exact hinj (Set.mem_Iio.mpr hxlt) (Set.mem_Iio.mpr hylt) hxy
  have hcard := Finset.card_le_card_of_injOn σe hmaps hinj'
  simpa [evenCompressedRankInParent, s] using hcard

/-- Odd analogue of `evenCompressedRankInParent_le_child_rank`. -/
theorem oddCompressedRankInParent_le_child_rank {N : ℕ} {σo σ : ℕ → ℕ}
    (hinj : Set.InjOn σo (Set.Iio (N / 2)))
    (hord : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j)) :
    ∀ i : ℕ, i < N / 2 → oddCompressedRankInParent σ N i ≤ σo i := by
  intro i hi
  classical
  let s := (Finset.range (N / 2)).filter (fun j => σ (2 * j + 1) < σ (2 * i + 1))
  have hmaps : Set.MapsTo σo (↑s) (↑(Finset.range (σo i))) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact Finset.mem_range.mpr ((hord j i (Finset.mem_range.mp hj'.1) hi).mp hj'.2)
  have hinj' : Set.InjOn σo (↑s) := by
    intro x hx y hy hxy
    have hxlt : x < N / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < N / 2 := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    exact hinj (Set.mem_Iio.mpr hxlt) (Set.mem_Iio.mpr hylt) hxy
  have hcard := Finset.card_le_card_of_injOn σo hmaps hinj'
  simpa [oddCompressedRankInParent, s] using hcard

/-- Child rank-credit bounds imply the even compressed-rank budget whenever the parent
preserves the even child order. -/
theorem EvenCompressedBound.of_child_bound {A N : ℕ} {σe σ : ℕ → ℕ}
    (hinj : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    (hord : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j))
    (hbound : ∀ i : ℕ, i < (N + 1) / 2 → σe i ≤ 2 * i + A) :
    EvenCompressedBound A σ N := by
  intro i hi
  exact (evenCompressedRankInParent_le_child_rank hinj hord i hi).trans (hbound i hi)

/-- Odd analogue of `EvenCompressedBound.of_child_bound`. -/
theorem OddCompressedBound.of_child_bound {A N : ℕ} {σo σ : ℕ → ℕ}
    (hinj : Set.InjOn σo (Set.Iio (N / 2)))
    (hord : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j))
    (hbound : ∀ i : ℕ, i < N / 2 → σo i ≤ 2 * i + A) :
    OddCompressedBound A σ N := by
  intro i hi
  exact (oddCompressedRankInParent_le_child_rank hinj hord i hi).trans (hbound i hi)

/-- Integer merge lag for an even value: actual parent rank minus the perfectly
alternating rank `2 * compressedRank`. Negative lag means the merge moved this even
value earlier than pure alternation would. -/
def evenMergeLag (σ : ℕ → ℕ) (N i : ℕ) : ℤ :=
  (σ (2 * i) : ℤ) - 2 * (evenCompressedRankInParent σ N i : ℤ)

/-- Integer child credit for an even value relative to the critical `2i+3` compressed
rank budget. The exact parent bound is `lag ≤ 2 * credit`. -/
def evenMergeCredit (σ : ℕ → ℕ) (N i : ℕ) : ℤ :=
  (2 * i + 3 : ℕ) - (evenCompressedRankInParent σ N i : ℤ)

/-- Pointwise even budget: local negative lag may pay for a local compressed-rank debt.
This is the exact arithmetic condition behind `σ (2i) ≤ 2*(2i)+6`. -/
def EvenPointwiseBudget (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < (N + 1) / 2 →
    evenMergeLag σ N i ≤ 2 * evenMergeCredit σ N i

/-- Integer merge lag for an odd value, measured from the perfectly alternating rank
`2 * compressedRank + 1`. -/
def oddMergeLag (σ : ℕ → ℕ) (N i : ℕ) : ℤ :=
  (σ (2 * i + 1) : ℤ) - (2 * (oddCompressedRankInParent σ N i : ℤ) + 1)

/-- Integer child credit for an odd value relative to the same critical `2i+3`
compressed-rank budget. The odd target has one extra unit of slack:
`lag ≤ 2 * credit + 1`. -/
def oddMergeCredit (σ : ℕ → ℕ) (N i : ℕ) : ℤ :=
  (2 * i + 3 : ℕ) - (oddCompressedRankInParent σ N i : ℤ)

/-- Pointwise odd budget. -/
def OddPointwiseBudget (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < N / 2 →
    oddMergeLag σ N i ≤ 2 * oddMergeCredit σ N i + 1

/-- Slot-level even budgets imply the parent `EvenPointwiseBudget`. -/
theorem evenPointwiseBudget_of_evenSlotBudget {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenSlot r < evenSlot s ↔ r < s))
    (hinj : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    (hbudget : EvenSlotPointwiseBudget N σe evenSlot) :
    EvenPointwiseBudget (slotMergeRank N σe σo evenSlot oddSlot) N := by
  intro i hi
  have hEq := evenCompressedRankInParent_slotMergeRank
    (N := N) (σe := σe) (σo := σo) (evenSlot := evenSlot) (oddSlot := oddSlot)
    hslot hinj hi
  simpa [evenMergeLag, evenMergeCredit, hEq] using hbudget i hi

/-- Slot-level odd budgets imply the parent `OddPointwiseBudget`. -/
theorem oddPointwiseBudget_of_oddSlotBudget {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hslot : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddSlot r < oddSlot s ↔ r < s))
    (hinj : Set.InjOn σo (Set.Iio (N / 2)))
    (hbudget : OddSlotPointwiseBudget N σo oddSlot) :
    OddPointwiseBudget (slotMergeRank N σe σo evenSlot oddSlot) N := by
  intro i hi
  have hEq := oddCompressedRankInParent_slotMergeRank
    (N := N) (σe := σe) (σo := σo) (evenSlot := evenSlot) (oddSlot := oddSlot)
    hslot hinj hi
  simpa [oddMergeLag, oddMergeCredit, hEq] using hbudget i hi

/-- The exact pointwise even budget implies the concrete `2v+6` bound on even values. -/
theorem even_bound_of_pointwise_budget {N : ℕ} {σ : ℕ → ℕ}
    (h : EvenPointwiseBudget σ N) :
    ∀ i : ℕ, i < (N + 1) / 2 → σ (2 * i) ≤ 2 * (2 * i) + 6 := by
  intro i hi
  have hZ := h i hi
  unfold evenMergeLag evenMergeCredit at hZ
  omega

/-- Conversely, the concrete even-value bound gives the exact pointwise credit budget.
Thus `EvenPointwiseBudget` is not extra magic; it is the same bound viewed through the
compressed-rank/lag decomposition. -/
theorem pointwise_budget_of_even_bound {N : ℕ} {σ : ℕ → ℕ}
    (h : ∀ i : ℕ, i < (N + 1) / 2 → σ (2 * i) ≤ 2 * (2 * i) + 6) :
    EvenPointwiseBudget σ N := by
  intro i hi
  have hN := h i hi
  unfold evenMergeLag evenMergeCredit
  omega

/-- Exact equivalence between the even pointwise budget and the concrete even bound. -/
theorem evenPointwiseBudget_iff_bound {N : ℕ} {σ : ℕ → ℕ} :
    EvenPointwiseBudget σ N ↔
      ∀ i : ℕ, i < (N + 1) / 2 → σ (2 * i) ≤ 2 * (2 * i) + 6 :=
  ⟨even_bound_of_pointwise_budget, pointwise_budget_of_even_bound⟩

/-- The exact pointwise odd budget implies the concrete `2v+6` bound on odd values. -/
theorem odd_bound_of_pointwise_budget {N : ℕ} {σ : ℕ → ℕ}
    (h : OddPointwiseBudget σ N) :
    ∀ i : ℕ, i < N / 2 → σ (2 * i + 1) ≤ 2 * (2 * i + 1) + 6 := by
  intro i hi
  have hZ := h i hi
  unfold oddMergeLag oddMergeCredit at hZ
  omega

/-- Conversely, the concrete odd-value bound gives the exact pointwise credit budget. -/
theorem pointwise_budget_of_odd_bound {N : ℕ} {σ : ℕ → ℕ}
    (h : ∀ i : ℕ, i < N / 2 → σ (2 * i + 1) ≤ 2 * (2 * i + 1) + 6) :
    OddPointwiseBudget σ N := by
  intro i hi
  have hN := h i hi
  unfold oddMergeLag oddMergeCredit
  omega

/-- Exact equivalence between the odd pointwise budget and the concrete odd bound. -/
theorem oddPointwiseBudget_iff_bound {N : ℕ} {σ : ℕ → ℕ} :
    OddPointwiseBudget σ N ↔
      ∀ i : ℕ, i < N / 2 → σ (2 * i + 1) ≤ 2 * (2 * i + 1) + 6 :=
  ⟨odd_bound_of_pointwise_budget, pointwise_budget_of_odd_bound⟩

/-- Combined exact pointwise budget theorem. This is the sharper replacement for the
coarse global `A,C` budget: it allows local negative merge lag to pay for local
compressed-rank debt, exactly as the finite witnesses do. -/
theorem two_mul_add_six_bound_of_pointwise_budget {N : ℕ} {σ : ℕ → ℕ}
    (he : EvenPointwiseBudget σ N) (ho : OddPointwiseBudget σ N) :
    ∀ v : ℕ, v < N → σ v ≤ twoMulAddSix v := by
  intro v hv
  rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
  · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero hv0
    have hi : i < (N + 1) / 2 := by omega
    simpa [twoMulAddSix, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      even_bound_of_pointwise_budget he i hi
  · set i := v / 2 with hiDef
    have hv_eq : v = 2 * i + 1 := by
      have h := (Nat.div_add_mod v 2).symm
      rw [hv1] at h
      simpa [hiDef, Nat.mul_comm] using h
    rw [hv_eq] at hv ⊢
    have hi : i < N / 2 := by omega
    simpa [twoMulAddSix, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      odd_bound_of_pointwise_budget ho i hi

/-- The even half of the parent merge has lag at most `C`: the parent rank of `2i` is
controlled by twice its compressed even rank plus `C`. A balanced parity merge word
should imply such a bound for a small `C`. -/
def EvenLagAtMost (C : ℕ) (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < (N + 1) / 2 → σ (2 * i) ≤ 2 * evenCompressedRankInParent σ N i + C

/-- The odd half of the parent merge has lag at most `C`. The extra `+1` is the rank
one expects from perfect alternation `E,O,E,O,...`. -/
def OddLagAtMost (C : ℕ) (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < N / 2 → σ (2 * i + 1) ≤ 2 * oddCompressedRankInParent σ N i + 1 + C

/-- Local budget calculation for even values. To make `σ (2i) ≤ 2*(2i)+6`, it suffices
that the even compressed child rank is bounded by `2i + A` and the merge lag is at most
`C`, with `2A + C ≤ 6`. This is the first analytic pressure point: a mere child bound
`2i+6` is too weak unless the lag is correspondingly negative or the child has slack. -/
theorem even_bound_of_compressed_bound_and_lag {A C N : ℕ} {σ : ℕ → ℕ}
    (hA : EvenCompressedBound A σ N) (hC : EvenLagAtMost C σ N)
    (hbudget : 2 * A + C ≤ 6) :
    ∀ i : ℕ, i < (N + 1) / 2 → σ (2 * i) ≤ 2 * (2 * i) + 6 := by
  intro i hi
  calc
    σ (2 * i) ≤ 2 * evenCompressedRankInParent σ N i + C := hC i hi
    _ ≤ 2 * (2 * i + A) + C := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hA i hi)) C
    _ ≤ 2 * (2 * i) + 6 := by omega

/-- Local budget calculation for odd values. The odd target is
`σ (2i+1) ≤ 2*(2i+1)+6 = 4i+8`, so the budget closes when `2A + C ≤ 7`. -/
theorem odd_bound_of_compressed_bound_and_lag {A C N : ℕ} {σ : ℕ → ℕ}
    (hA : OddCompressedBound A σ N) (hC : OddLagAtMost C σ N)
    (hbudget : 2 * A + C ≤ 7) :
    ∀ i : ℕ, i < N / 2 → σ (2 * i + 1) ≤ 2 * (2 * i + 1) + 6 := by
  intro i hi
  calc
    σ (2 * i + 1) ≤ 2 * oddCompressedRankInParent σ N i + 1 + C := hC i hi
    _ ≤ 2 * (2 * i + A) + 1 + C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hA i hi)) 1) C
    _ ≤ 2 * (2 * i + 1) + 6 := by omega

/-- Combined parent-bound theorem for a balanced dyadic merge. This theorem is not a
construction; it is the arithmetic budget that any proposed recursive invariant must
satisfy to preserve the concrete SAT-supported bound `2v+6`. -/
theorem two_mul_add_six_bound_of_compressed_bounds_and_lag {Ae Ao Ce Co N : ℕ}
    {σ : ℕ → ℕ}
    (heA : EvenCompressedBound Ae σ N) (heC : EvenLagAtMost Ce σ N)
    (hoA : OddCompressedBound Ao σ N) (hoC : OddLagAtMost Co σ N)
    (heBudget : 2 * Ae + Ce ≤ 6) (hoBudget : 2 * Ao + Co ≤ 7) :
    ∀ v : ℕ, v < N → σ v ≤ 2 * v + 6 := by
  intro v hv
  rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
  · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero hv0
    have hi : i < (N + 1) / 2 := by omega
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      even_bound_of_compressed_bound_and_lag heA heC heBudget i hi
  · set i := v / 2 with hiDef
    have hv_eq : v = 2 * i + 1 := by
      have h := (Nat.div_add_mod v 2).symm
      rw [hv1] at h
      simpa [hiDef, Nat.mul_comm] using h
    rw [hv_eq] at hv ⊢
    have hi : i < N / 2 := by omega
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      odd_bound_of_compressed_bound_and_lag hoA hoC hoBudget i hi

/-- A proof-shaped dyadic merge step for the prepared invariant. The parent preserves
the internal order of the two prepared children, satisfies a compressed-rank/merge-lag
budget strong enough to recover `σ v ≤ 2v+6`, and proves odd-difference safety in the
informative split form (`EndpointOrientationDisagree ∨ MergeZigzag`). This is now the
main construction object to try to build. -/
def GoodDyadicMergeStep (Ae Ao Ce Co N : ℕ) (σe σo σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (Set.Iio N) ∧
  (∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
    (σ (2 * i) < σ (2 * j) ↔ σe i < σe j)) ∧
  (∀ i j : ℕ, i < N / 2 → j < N / 2 →
    (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j)) ∧
  EvenCompressedBound Ae σ N ∧
  EvenLagAtMost Ce σ N ∧
  OddCompressedBound Ao σ N ∧
  OddLagAtMost Co σ N ∧
  2 * Ae + Ce ≤ 6 ∧
  2 * Ao + Co ≤ 7 ∧
  OddAPSplitSafe σ N

/-- Sharper prepared merge step using the exact pointwise credit/lag budget. This is
the realistic version suggested by the witnesses: local negative lag can pay for local
compressed-rank debt, so no uniform child-credit constant is required. -/
def ExactGoodDyadicMergeStep (N : ℕ) (σe σo σ : ℕ → ℕ) : Prop :=
  Set.InjOn σ (Set.Iio N) ∧
  (∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
    (σ (2 * i) < σ (2 * j) ↔ σe i < σe j)) ∧
  (∀ i j : ℕ, i < N / 2 → j < N / 2 →
    (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j)) ∧
  EvenPointwiseBudget σ N ∧
  OddPointwiseBudget σ N ∧
  OddAPSplitSafe σ N

/-- Constructor for `ExactGoodDyadicMergeStep` from a slot merge. This is the current
construction-facing interface: choose increasing, disjoint even/odd slot maps satisfying
the exact pointwise deadlines, then prove the odd-AP split certificate for the resulting
parent order. -/
theorem exactGoodDyadicMergeStep_of_slotMergeRank {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hinje : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    (hinjo : Set.InjOn σo (Set.Iio (N / 2)))
    (hslotE : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenSlot r < evenSlot s ↔ r < s))
    (hslotO : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddSlot r < oddSlot s ↔ r < s))
    (hdisj : ∀ r s : ℕ, r < (N + 1) / 2 → s < N / 2 →
      evenSlot r ≠ oddSlot s)
    (heBudget : EvenSlotPointwiseBudget N σe evenSlot)
    (hoBudget : OddSlotPointwiseBudget N σo oddSlot)
    (hSplit : OddAPSplitSafe (slotMergeRank N σe σo evenSlot oddSlot) N) :
    ExactGoodDyadicMergeStep N σe σo
      (slotMergeRank N σe σo evenSlot oddSlot) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hSplit⟩
  · exact slotMergeRank_injOn hinje hinjo hslotE hslotO hdisj
  · exact slotMergeRank_even_order hslotE hinje
  · exact slotMergeRank_odd_order hslotO hinjo
  · exact evenPointwiseBudget_of_evenSlotBudget hslotE hinje heBudget
  · exact oddPointwiseBudget_of_oddSlotBudget hslotO hinjo hoBudget

/-- Packaged version of `exactGoodDyadicMergeStep_of_slotMergeRank` using the named
slot-compatibility predicate. -/
theorem exactGoodDyadicMergeStep_of_slotMergeCompatible {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (hinje : Set.InjOn σe (Set.Iio ((N + 1) / 2)))
    (hinjo : Set.InjOn σo (Set.Iio (N / 2)))
    (hm : SlotMergeCompatible N σe σo evenSlot oddSlot) :
    ExactGoodDyadicMergeStep N σe σo
      (slotMergeRank N σe σo evenSlot oddSlot) := by
  exact exactGoodDyadicMergeStep_of_slotMergeRank hinje hinjo
    hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1 hm.2.2.2.2.2

/-- Internal-order preservation transfers `Mono4` from the even child of the parent
back to the even input witness. -/
theorem mono4_evenChild_of_dyadicMergeStep {f : ℕ → ℕ} {N : ℕ}
    {σe σo σ : ℕ → ℕ} (h : DyadicMergeStep f N σe σo σ)
    {a d : ℕ} (hN : a + 3 * d < (N + 1) / 2) :
    Mono4 (evenChild σ) a d → Mono4 σe a d := by
  intro hmono
  have h0 : a < (N + 1) / 2 := by omega
  have h1 : a + d < (N + 1) / 2 := by omega
  have h2 : a + 2 * d < (N + 1) / 2 := by omega
  have h3 : a + 3 * d < (N + 1) / 2 := hN
  rcases hmono with ⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩
  · exact Or.inl
      ⟨(h.2.2.1 a (a + d) h0 h1).mp h01,
       (h.2.2.1 (a + d) (a + 2 * d) h1 h2).mp h12,
       (h.2.2.1 (a + 2 * d) (a + 3 * d) h2 h3).mp h23⟩
  · exact Or.inr
      ⟨(h.2.2.1 (a + 3 * d) (a + 2 * d) h3 h2).mp h32,
       (h.2.2.1 (a + 2 * d) (a + d) h2 h1).mp h21,
       (h.2.2.1 (a + d) a h1 h0).mp h10⟩

/-- Internal-order preservation transfers `Mono4` from the odd child of the parent
back to the odd input witness. -/
theorem mono4_oddChild_of_dyadicMergeStep {f : ℕ → ℕ} {N : ℕ}
    {σe σo σ : ℕ → ℕ} (h : DyadicMergeStep f N σe σo σ)
    {a d : ℕ} (hN : a + 3 * d < N / 2) :
    Mono4 (oddChild σ) a d → Mono4 σo a d := by
  intro hmono
  have h0 : a < N / 2 := by omega
  have h1 : a + d < N / 2 := by omega
  have h2 : a + 2 * d < N / 2 := by omega
  have h3 : a + 3 * d < N / 2 := hN
  rcases hmono with ⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩
  · exact Or.inl
      ⟨(h.2.2.2.1 a (a + d) h0 h1).mp h01,
       (h.2.2.2.1 (a + d) (a + 2 * d) h1 h2).mp h12,
       (h.2.2.2.1 (a + 2 * d) (a + 3 * d) h2 h3).mp h23⟩
  · exact Or.inr
      ⟨(h.2.2.2.1 (a + 3 * d) (a + 2 * d) h3 h2).mp h32,
       (h.2.2.2.1 (a + 2 * d) (a + d) h2 h1).mp h21,
       (h.2.2.2.1 (a + d) a h1 h0).mp h10⟩

/-- A flexible dyadic merge step upgrades child merge witnesses to a parent merge
witness. This is the adapter the construction search should target: once a candidate
merge gives `DyadicMergeStep`, the child freeness and parent `MergeWitness` fields are
automatic. -/
theorem mergeWitness_of_dyadicMergeStep {f fe fo : ℕ → ℕ} {N : ℕ}
    {σe σo σ : ℕ → ℕ}
    (he : MergeWitness fe ((N + 1) / 2) σe)
    (ho : MergeWitness fo (N / 2) σo)
    (hm : DyadicMergeStep f N σe σo σ) :
    MergeWitness f N σ := by
  refine ⟨hm.1, hm.2.1, ?_, ?_, hm.2.2.2.2⟩
  · have hfree : ¬ HasMono4 σe ((N + 1) / 2) :=
      not_hasMono4_of_child_orders_edgeBreak he.2.2.1 he.2.2.2.1 he.2.2.2.2
    rintro ⟨a, d, hd, hN, hmono⟩
    exact hfree ⟨a, d, hd, hN, mono4_evenChild_of_dyadicMergeStep hm hN hmono⟩
  · have hfree : ¬ HasMono4 σo (N / 2) :=
      not_hasMono4_of_child_orders_edgeBreak ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2
    rintro ⟨a, d, hd, hN, hmono⟩
    exact hfree ⟨a, d, hd, hN, mono4_oddChild_of_dyadicMergeStep hm hN hmono⟩

/-- A good dyadic merge step turns two prepared child witnesses into a prepared parent
witness. This is the direct recursive closure lemma for any concrete merge construction
that can satisfy the lag-budget and split-safety fields. -/
theorem goodWitness_of_goodDyadicMergeStep {Ae Ao Ce Co N : ℕ} {σe σo σ : ℕ → ℕ}
    (he : GoodWitness ((N + 1) / 2) σe)
    (ho : GoodWitness (N / 2) σo)
    (hm : GoodDyadicMergeStep Ae Ao Ce Co N σe σo σ) :
    GoodWitness N σ := by
  rcases hm with
    ⟨hinj, hEvenOrd, hOddOrd, heComp, heLag, hoComp, hoLag, heBudget, hoBudget, hSplit⟩
  have hBound : ∀ v : ℕ, v < N → σ v ≤ twoMulAddSix v := by
    simpa [twoMulAddSix] using
      two_mul_add_six_bound_of_compressed_bounds_and_lag
        heComp heLag hoComp hoLag heBudget hoBudget
  have hEdge : OddDiffEdgeBreakSafe σ N := OddDiffEdgeBreakSafe.of_splitSafe hSplit
  have hMerge : DyadicMergeStep twoMulAddSix N σe σo σ :=
    ⟨hinj, hBound, hEvenOrd, hOddOrd, hEdge⟩
  refine ⟨hinj, hBound, ?_, ?_, hSplit⟩
  · have hfree : ¬ HasMono4 σe ((N + 1) / 2) :=
      (finiteFeasible_witness_of_goodWitness he).2.2
    rintro ⟨a, d, hd, hN, hmono⟩
    exact hfree ⟨a, d, hd, hN, mono4_evenChild_of_dyadicMergeStep hMerge hN hmono⟩
  · have hfree : ¬ HasMono4 σo (N / 2) :=
      (finiteFeasible_witness_of_goodWitness ho).2.2
    rintro ⟨a, d, hd, hN, hmono⟩
    exact hfree ⟨a, d, hd, hN, mono4_oddChild_of_dyadicMergeStep hMerge hN hmono⟩

/-- Exact pointwise-budget merge step turns prepared children into a prepared parent.
This is the currently preferred closure lemma for the main construction. -/
theorem goodWitness_of_exactGoodDyadicMergeStep {N : ℕ} {σe σo σ : ℕ → ℕ}
    (he : GoodWitness ((N + 1) / 2) σe)
    (ho : GoodWitness (N / 2) σo)
    (hm : ExactGoodDyadicMergeStep N σe σo σ) :
    GoodWitness N σ := by
  rcases hm with ⟨hinj, hEvenOrd, hOddOrd, heBudget, hoBudget, hSplit⟩
  have hBound : ∀ v : ℕ, v < N → σ v ≤ twoMulAddSix v :=
    two_mul_add_six_bound_of_pointwise_budget heBudget hoBudget
  have hEdge : OddDiffEdgeBreakSafe σ N := OddDiffEdgeBreakSafe.of_splitSafe hSplit
  have hMerge : DyadicMergeStep twoMulAddSix N σe σo σ :=
    ⟨hinj, hBound, hEvenOrd, hOddOrd, hEdge⟩
  refine ⟨hinj, hBound, ?_, ?_, hSplit⟩
  · have hfree : ¬ HasMono4 σe ((N + 1) / 2) :=
      (finiteFeasible_witness_of_goodWitness he).2.2
    rintro ⟨a, d, hd, hN, hmono⟩
    exact hfree ⟨a, d, hd, hN, mono4_evenChild_of_dyadicMergeStep hMerge hN hmono⟩
  · have hfree : ¬ HasMono4 σo (N / 2) :=
      (finiteFeasible_witness_of_goodWitness ho).2.2
    rintro ⟨a, d, hd, hN, hmono⟩
    exact hfree ⟨a, d, hd, hN, mono4_oddChild_of_dyadicMergeStep hMerge hN hmono⟩

/-- A slot-compatible merge of two prepared children is a prepared parent witness. -/
theorem goodWitness_of_slotMergeCompatible {N : ℕ}
    {σe σo evenSlot oddSlot : ℕ → ℕ}
    (he : GoodWitness ((N + 1) / 2) σe)
    (ho : GoodWitness (N / 2) σo)
    (hm : SlotMergeCompatible N σe σo evenSlot oddSlot) :
    GoodWitness N (slotMergeRank N σe σo evenSlot oddSlot) :=
  goodWitness_of_exactGoodDyadicMergeStep he ho
    (exactGoodDyadicMergeStep_of_slotMergeCompatible he.1 ho.1 hm)

/-- A merge witness is, in particular, a finite-feasibility witness. -/
theorem finiteFeasible_witness_of_mergeWitness {f : ℕ → ℕ} {N : ℕ} {σ : ℕ → ℕ}
    (h : MergeWitness f N σ) :
    Set.InjOn σ (Set.Iio N) ∧ (∀ v < N, σ v ≤ f v) ∧ ¬ HasMono4 σ N := by
  exact ⟨h.1, h.2.1,
    not_hasMono4_of_child_orders_edgeBreak h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

/-- Any ordinary finite-feasibility witness can be repackaged as a parity-merge
witness: parent freeness implies the two child freeness statements, and odd-difference
edge breaks are just a normal form for odd-difference non-monotonicity. -/
theorem mergeWitness_of_finiteFeasible_witness {f : ℕ → ℕ} {N : ℕ} {σ : ℕ → ℕ}
    (h : Set.InjOn σ (Set.Iio N) ∧ (∀ v < N, σ v ≤ f v) ∧ ¬ HasMono4 σ N) :
    MergeWitness f N σ :=
  ⟨h.1, h.2.1, not_hasMono4_evenChild h.2.2, not_hasMono4_oddChild h.2.2,
    (OddDiffSafe.of_not_hasMono4 h.2.2).edgeBreakSafe⟩

/-- `MergeWitness` is equivalent to the ordinary finite-feasibility witness, but exposes
the dyadic subgoals needed by the construction program. -/
theorem mergeWitness_iff_finiteFeasible_witness {f : ℕ → ℕ} {N : ℕ} {σ : ℕ → ℕ} :
    MergeWitness f N σ ↔
      Set.InjOn σ (Set.Iio N) ∧ (∀ v < N, σ v ≤ f v) ∧ ¬ HasMono4 σ N :=
  ⟨finiteFeasible_witness_of_mergeWitness, mergeWitness_of_finiteFeasible_witness⟩

/-- It suffices to build a bounded parity-merge witness at every finite level. -/
theorem finiteFeasible_of_mergeWitness {f : ℕ → ℕ}
    (h : ∀ N : ℕ, ∃ σ : ℕ → ℕ, MergeWitness f N σ) :
    FiniteFeasible f := by
  intro N
  obtain ⟨σ, hσ⟩ := h N
  exact ⟨σ, finiteFeasible_witness_of_mergeWitness hσ⟩

/-- The empty initial segment has a canonical merge witness for every bound. -/
theorem mergeWitness_zero (f : ℕ → ℕ) : MergeWitness f 0 (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact False.elim (Nat.not_lt_zero x (Set.mem_Iio.mp hx))
  · intro v hv
    omega
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · intro a d hd _hdodd hN
    omega

/-- The singleton initial segment has a canonical merge witness for every bound. -/
theorem mergeWitness_one (f : ℕ → ℕ) : MergeWitness f 1 (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy _hxy
    have hxlt : x < 1 := Set.mem_Iio.mp hx
    have hylt : y < 1 := Set.mem_Iio.mp hy
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    omega
  · intro v hv
    exact Nat.zero_le (f v)
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · intro a d hd _hdodd hN
    omega

/-- The empty initial segment is a prepared witness. -/
theorem goodWitness_zero : GoodWitness 0 (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact False.elim (Nat.not_lt_zero x (Set.mem_Iio.mp hx))
  · intro v hv
    omega
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · intro a d hd _hdodd hN
    omega

/-- The singleton initial segment is a prepared witness. -/
theorem goodWitness_one : GoodWitness 1 (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy _hxy
    have hxlt : x < 1 := Set.mem_Iio.mp hx
    have hylt : y < 1 := Set.mem_Iio.mp hy
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    omega
  · intro v hv
    exact Nat.zero_le (twoMulAddSix v)
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · rintro ⟨a, d, hd, hN, _hmono⟩
    omega
  · intro a d hd _hdodd hN
    omega

/-- The empty initial segment is an anchored concrete witness. -/
theorem anchoredConcreteWitness_zero : AnchoredConcreteWitness 0 (fun _ => 0) :=
  ⟨concreteWitness_of_goodWitness goodWitness_zero, rfl⟩

/-- The singleton initial segment is an anchored concrete witness. -/
theorem anchoredConcreteWitness_one : AnchoredConcreteWitness 1 (fun _ => 0) :=
  ⟨concreteWitness_of_goodWitness goodWitness_one, rfl⟩

section ConstructionTargets
/-! ## Construction-side reductions (exploratory; all conditional on the open merge step)

The theorems in this section reduce `FiniteFeasible` / `Erdos196Avoidable` to an
*undischarged* per-level merge hypothesis `hstep` (build a parent order from its two prepared
parity children). **None of them feeds the headline `exists_finiteFeasible_iff_avoidable` or
any unconditional result.** They are a menu of equivalent target shapes for a future
construction — kept rather than pruned because discharging the merge may be easiest against
one particular shape, and which one is not yet known. The cleanest statement of the remaining
gap is `mono4_free_iff_forall_avoidV2` / `erdos196Avoidable_iff_exists_injective_avoidV2_all`
(`OddDifference.lean`): the open content is the quantifier swap `(∀ k ∃ G) ⟹ (∃ G ∀ k)`. -/

/-- Prepared witnesses at every finite level imply finite feasibility for the concrete
bound. -/
theorem finiteFeasible_of_goodWitness
    (h : ∀ N : ℕ, ∃ σ : ℕ → ℕ, GoodWitness N σ) :
    FiniteFeasible twoMulAddSix := by
  intro N
  obtain ⟨σ, hσ⟩ := h N
  exact ⟨σ, finiteFeasible_witness_of_goodWitness hσ⟩

/-- Strong-recursion constructor for prepared witnesses. -/
theorem finiteFeasible_of_strong_goodWitness
    (hstep : ∀ N : ℕ,
      (∀ M : ℕ, M < N → ∃ τ : ℕ → ℕ, GoodWitness M τ) →
        ∃ σ : ℕ → ℕ, GoodWitness N σ) :
    FiniteFeasible twoMulAddSix :=
  finiteFeasible_of_goodWitness (fun N => Nat.strongRecOn N hstep)

/-- Dyadic-recursion constructor for prepared witnesses. This is the theorem-shaped
version of the remaining attack: close `GoodWitness` under merging the two prepared
parity children. -/
theorem finiteFeasible_of_child_goodWitness
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, GoodWitness ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, GoodWitness (N / 2) σo) →
        ∃ σ : ℕ → ℕ, GoodWitness N σ) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_strong_goodWitness
  intro N ih
  rcases lt_trichotomy N 1 with hN | hN | hN
  · have h0 : N = 0 := by omega
    subst h0
    exact ⟨fun _ => 0, goodWitness_zero⟩
  · subst hN
    exact ⟨fun _ => 0, goodWitness_one⟩
  · have h2 : 2 ≤ N := by omega
    exact hstep N h2
      (ih ((N + 1) / 2) (by omega))
      (ih (N / 2) (by omega))

/-- A prepared witness carrying an additional construction invariant `P`. This is the
pivot away from the too-strong "merge arbitrary prepared children" target: future work
can choose `P` to express deadline-aware/canonical mergeability. -/
def CompatibleGoodWitness (P : ℕ → (ℕ → ℕ) → Prop) (N : ℕ) (σ : ℕ → ℕ) : Prop :=
  GoodWitness N σ ∧ P N σ

/-- Dyadic recursion with an extra invariant. If the invariant holds at the two base
levels and closes under the child merge, then the underlying `GoodWitness` family still
gives finite feasibility. -/
theorem finiteFeasible_of_child_compatibleGoodWitness
    {P : ℕ → (ℕ → ℕ) → Prop}
    (h0 : P 0 (fun _ => 0))
    (h1 : P 1 (fun _ => 0))
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, CompatibleGoodWitness P ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, CompatibleGoodWitness P (N / 2) σo) →
        ∃ σ : ℕ → ℕ, CompatibleGoodWitness P N σ) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_goodWitness
  intro N
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, CompatibleGoodWitness P N σ := by
    exact Nat.strongRecOn
      (motive := fun N => ∃ σ : ℕ → ℕ, CompatibleGoodWitness P N σ) N (fun N ih => by
    rcases lt_trichotomy N 1 with hN | hN | hN
    · have h0N : N = 0 := by omega
      subst h0N
      exact ⟨fun _ => 0, goodWitness_zero, h0⟩
    · subst hN
      exact ⟨fun _ => 0, goodWitness_one, h1⟩
    · have h2 : 2 ≤ N := by omega
      exact hstep N h2
        (ih ((N + 1) / 2) (by omega))
        (ih (N / 2) (by omega)))
  exact ⟨σ, hσ.1⟩

/-- Slot-merge version of the invariant recursion. The remaining construction problem
can now be phrased as finding an invariant `P` and, for compatible children, slots that
are `SlotMergeCompatible` and whose parent still satisfies `P`. -/
theorem finiteFeasible_of_child_compatibleSlotMerge
    {P : ℕ → (ℕ → ℕ) → Prop}
    (h0 : P 0 (fun _ => 0))
    (h1 : P 1 (fun _ => 0))
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness P ((N + 1) / 2) σe →
      CompatibleGoodWitness P (N / 2) σo →
        ∃ evenSlot oddSlot : ℕ → ℕ,
          SlotMergeCompatible N σe σo evenSlot oddSlot ∧
          P N (slotMergeRank N σe σo evenSlot oddSlot)) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_compatibleGoodWitness h0 h1
  intro N hN he ho
  obtain ⟨σe, hσe⟩ := he
  obtain ⟨σo, hσo⟩ := ho
  obtain ⟨evenSlot, oddSlot, hMerge, hP⟩ := hstep N hN σe σo hσe hσo
  exact ⟨slotMergeRank N σe σo evenSlot oddSlot,
    goodWitness_of_slotMergeCompatible hσe.1 hσo.1 hMerge, hP⟩

/-- Even-position-set version of the invariant recursion. A future construction can
specify only the finite set of parent positions occupied by the even stream; the odd
stream is its complement, and `orderEmbOfFin` supplies the slot maps. -/
theorem finiteFeasible_of_child_compatibleEvenPositionSet
    {P : ℕ → (ℕ → ℕ) → Prop}
    (h0 : P 0 (fun _ => 0))
    (h1 : P 1 (fun _ => 0))
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness P ((N + 1) / 2) σe →
      CompatibleGoodWitness P (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          EvenSlotPointwiseBudget N σe (evenPositionSlot N E hE) ∧
          OddSlotPointwiseBudget N σo (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N ∧
          P N (slotMergeRank N σe σo (evenPositionSlot N E hE)
            (oddPositionSlot N E hE))) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_compatibleSlotMerge h0 h1
  intro N hN σe σo hσe hσo
  obtain ⟨E, hE, heBudget, hoBudget, hSplit, hP⟩ := hstep N hN σe σo hσe hσo
  refine ⟨evenPositionSlot N E hE, oddPositionSlot N E hE, ?_, hP⟩
  exact slotMergeCompatible_of_evenPositionSet hE heBudget hoBudget hSplit

/-- The empty witness is anchored. -/
theorem anchored_zero : Anchored 0 (fun _ => 0) := rfl

/-- The singleton witness is anchored. -/
theorem anchored_one : Anchored 1 (fun _ => 0) := rfl

/-- Anchored concrete pivot theorem. This is the current construction-facing target:
given anchored prepared children, choose the parent positions of the even stream so
that value `0` remains first, the concrete `2v+6` slot deadlines hold, and odd APs
split. No auxiliary scale-tight deadline is required. -/
theorem finiteFeasible_of_child_anchoredConcreteEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness Anchored ((N + 1) / 2) σe →
      CompatibleGoodWitness Anchored (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_compatibleEvenPositionSet
    (P := Anchored) anchored_zero anchored_one
  intro N hN σe σo hσe hσo
  obtain ⟨E, hE, hslot0, hConcrete, hSplit⟩ := hstep N hN σe σo hσe hσo
  refine ⟨E, hE, ?_, ?_, hSplit, ?_⟩
  · exact evenSlotPointwiseBudget_of_concreteSlotBound hConcrete
  · exact oddSlotPointwiseBudget_of_concreteSlotBound hConcrete
  · exact anchored_slotMergeRank_of_slot0 hσe.2 hslot0

/-- Bad-shuffle form of the anchored concrete pivot theorem. This is the most local
current construction target: choose the even-position set, prove the concrete deadlines,
and prove the orientation-aware bad-shuffle condition. Injectivity of the slot merge
then upgrades the bad-shuffle condition to `OddAPSplitSafe`. -/
theorem finiteFeasible_of_child_anchoredConcreteBadShuffleEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness Anchored ((N + 1) / 2) σe →
      CompatibleGoodWitness Anchored (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          BadShuffleAvoiding
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_anchoredConcreteEvenPositionSet
  intro N hN σe σo hσe hσo
  obtain ⟨E, hE, hslot0, hConcrete, hBad⟩ := hstep N hN σe σo hσe hσo
  refine ⟨E, hE, hslot0, hConcrete, ?_⟩
  apply OddAPSplitSafe.of_badShuffleAvoiding
  · exact slotMergeRank_injOn hσe.1.1 hσo.1.1
      (fun r s hr hs => finSlot_lt_iff hr hs)
      (fun r s hr hs => finSlot_lt_iff hr hs)
      (fun r s hr hs =>
        finSlot_ne_of_disjoint (s := E) (t := Eᶜ)
          (hs := hE)
          (ht := by
            rw [Finset.card_compl, hE]
            simp
            omega)
          disjoint_compl_right hr hs)
  · exact hBad

/-- Merging two merely concrete child witnesses is enough: the split certificate is
only needed for the parent merge, not as recursive child data. This is the socket that
matches the direct finite witnesses more closely than `GoodWitness` recursion. -/
theorem anchoredConcreteWitness_of_evenPositionSet_badShuffle {N : ℕ}
    {σe σo : ℕ → ℕ} {E : Finset (Fin N)} {hE : E.card = (N + 1) / 2}
    (he : AnchoredConcreteWitness ((N + 1) / 2) σe)
    (ho : AnchoredConcreteWitness (N / 2) σo)
    (hslot0 : evenPositionSlot N E hE 0 = 0)
    (hConcrete :
      ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE))
    (hBad :
      BadShuffleAvoiding
        (slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE)) N) :
    AnchoredConcreteWitness N
      (slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE)) := by
  classical
  let σ := slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE)
  have hslotE : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenPositionSlot N E hE r < evenPositionSlot N E hE s ↔ r < s) :=
    fun r s hr hs => finSlot_lt_iff hr hs
  have hslotO : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddPositionSlot N E hE r < oddPositionSlot N E hE s ↔ r < s) :=
    fun r s hr hs => finSlot_lt_iff hr hs
  have hdisj : ∀ r s : ℕ, r < (N + 1) / 2 → s < N / 2 →
      evenPositionSlot N E hE r ≠ oddPositionSlot N E hE s := by
    intro r s hr hs
    exact finSlot_ne_of_disjoint (s := E) (t := Eᶜ)
      (hs := hE)
      (ht := by
        rw [Finset.card_compl, hE]
        simp
        omega)
      disjoint_compl_right hr hs
  have hinj : Set.InjOn σ (Set.Iio N) :=
    slotMergeRank_injOn he.1.1 ho.1.1 hslotE hslotO hdisj
  have hEvenOrd : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j) :=
    slotMergeRank_even_order hslotE he.1.1
  have hOddOrd : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j) :=
    slotMergeRank_odd_order hslotO ho.1.1
  have hBound : ∀ v : ℕ, v < N → σ v ≤ twoMulAddSix v := by
    intro v hv
    rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
    · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero hv0
      have hi : i < (N + 1) / 2 := by omega
      simpa [σ] using hConcrete.1 i hi
    · set i := v / 2 with hiDef
      have hv_eq : v = 2 * i + 1 := by
        have h := (Nat.div_add_mod v 2).symm
        rw [hv1] at h
        simpa [hiDef, Nat.mul_comm] using h
      rw [hv_eq] at hv ⊢
      have hi : i < N / 2 := by omega
      simpa [σ] using hConcrete.2 i hi
  have hSplit : OddAPSplitSafe σ N :=
    OddAPSplitSafe.of_badShuffleAvoiding hinj hBad
  have hEdge : OddDiffEdgeBreakSafe σ N :=
    OddDiffEdgeBreakSafe.of_splitSafe hSplit
  have hMerge : DyadicMergeStep twoMulAddSix N σe σo σ :=
    ⟨hinj, hBound, hEvenOrd, hOddOrd, hEdge⟩
  have hEvenFree : ¬ HasMono4 (evenChild σ) ((N + 1) / 2) := by
    rintro ⟨a, d, hd, hN, hmono⟩
    exact he.1.2.2 ⟨a, d, hd, hN,
      mono4_evenChild_of_dyadicMergeStep hMerge hN hmono⟩
  have hOddFree : ¬ HasMono4 (oddChild σ) (N / 2) := by
    rintro ⟨a, d, hd, hN, hmono⟩
    exact ho.1.2.2 ⟨a, d, hd, hN,
      mono4_oddChild_of_dyadicMergeStep hMerge hN hmono⟩
  have hFree : ¬ HasMono4 σ N :=
    not_hasMono4_of_child_orders_edgeBreak hEvenFree hOddFree hEdge
  refine ⟨⟨hinj, hBound, hFree⟩, ?_⟩
  exact slotMergeRank_zero_of_child_zero he.2 hslot0

/-- Odd-difference-safe version of the concrete merge theorem. This is weaker than the
bad-shuffle certificate: it asks only for the exact property needed to combine two
4-AP-free children into a 4-AP-free parent. -/
theorem anchoredConcreteWitness_of_evenPositionSet_oddDiffSafe {N : ℕ}
    {σe σo : ℕ → ℕ} {E : Finset (Fin N)} {hE : E.card = (N + 1) / 2}
    (he : AnchoredConcreteWitness ((N + 1) / 2) σe)
    (ho : AnchoredConcreteWitness (N / 2) σo)
    (hslot0 : evenPositionSlot N E hE 0 = 0)
    (hConcrete :
      ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE))
    (hOddDiff :
      OddDiffSafe
        (slotMergeRank N σe σo (evenPositionSlot N E hE)
          (oddPositionSlot N E hE)) N) :
    AnchoredConcreteWitness N
      (slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE)) := by
  classical
  let σ := slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE)
  have hslotE : ∀ r s : ℕ, r < (N + 1) / 2 → s < (N + 1) / 2 →
      (evenPositionSlot N E hE r < evenPositionSlot N E hE s ↔ r < s) :=
    fun r s hr hs => finSlot_lt_iff hr hs
  have hslotO : ∀ r s : ℕ, r < N / 2 → s < N / 2 →
      (oddPositionSlot N E hE r < oddPositionSlot N E hE s ↔ r < s) :=
    fun r s hr hs => finSlot_lt_iff hr hs
  have hdisj : ∀ r s : ℕ, r < (N + 1) / 2 → s < N / 2 →
      evenPositionSlot N E hE r ≠ oddPositionSlot N E hE s := by
    intro r s hr hs
    exact finSlot_ne_of_disjoint (s := E) (t := Eᶜ)
      (hs := hE)
      (ht := by
        rw [Finset.card_compl, hE]
        simp
        omega)
      disjoint_compl_right hr hs
  have hinj : Set.InjOn σ (Set.Iio N) :=
    slotMergeRank_injOn he.1.1 ho.1.1 hslotE hslotO hdisj
  have hEvenOrd : ∀ i j : ℕ, i < (N + 1) / 2 → j < (N + 1) / 2 →
      (σ (2 * i) < σ (2 * j) ↔ σe i < σe j) :=
    slotMergeRank_even_order hslotE he.1.1
  have hOddOrd : ∀ i j : ℕ, i < N / 2 → j < N / 2 →
      (σ (2 * i + 1) < σ (2 * j + 1) ↔ σo i < σo j) :=
    slotMergeRank_odd_order hslotO ho.1.1
  have hBound : ∀ v : ℕ, v < N → σ v ≤ twoMulAddSix v := by
    intro v hv
    rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
    · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero hv0
      have hi : i < (N + 1) / 2 := by omega
      simpa [σ] using hConcrete.1 i hi
    · set i := v / 2 with hiDef
      have hv_eq : v = 2 * i + 1 := by
        have h := (Nat.div_add_mod v 2).symm
        rw [hv1] at h
        simpa [hiDef, Nat.mul_comm] using h
      rw [hv_eq] at hv ⊢
      have hi : i < N / 2 := by omega
      simpa [σ] using hConcrete.2 i hi
  have hEdge : OddDiffEdgeBreakSafe σ N := hOddDiff.edgeBreakSafe
  have hMerge : DyadicMergeStep twoMulAddSix N σe σo σ :=
    ⟨hinj, hBound, hEvenOrd, hOddOrd, hEdge⟩
  have hEvenFree : ¬ HasMono4 (evenChild σ) ((N + 1) / 2) := by
    rintro ⟨a, d, hd, hN, hmono⟩
    exact he.1.2.2 ⟨a, d, hd, hN,
      mono4_evenChild_of_dyadicMergeStep hMerge hN hmono⟩
  have hOddFree : ¬ HasMono4 (oddChild σ) (N / 2) := by
    rintro ⟨a, d, hd, hN, hmono⟩
    exact ho.1.2.2 ⟨a, d, hd, hN,
      mono4_oddChild_of_dyadicMergeStep hMerge hN hmono⟩
  have hFree : ¬ HasMono4 σ N :=
    not_hasMono4_of_child_orders hEvenFree hOddFree hOddDiff
  refine ⟨⟨hinj, hBound, hFree⟩, ?_⟩
  exact slotMergeRank_zero_of_child_zero he.2 hslot0

/-- Existential concrete-witness recursion. Unlike the `CompatibleGoodWitness` slot
targets, this does not require every pair of prepared children to merge, and it does
not require child witnesses to carry the parent-style split certificate. -/
theorem finiteFeasible_of_child_anchoredConcreteWitnessBadShuffleEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, AnchoredConcreteWitness ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, AnchoredConcreteWitness (N / 2) σo) →
        ∃ σe σo : ℕ → ℕ, ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          AnchoredConcreteWitness ((N + 1) / 2) σe ∧
          AnchoredConcreteWitness (N / 2) σo ∧
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          BadShuffleAvoiding
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    FiniteFeasible twoMulAddSix := by
  intro N
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, AnchoredConcreteWitness N σ := by
    exact Nat.strongRecOn
      (motive := fun N => ∃ σ : ℕ → ℕ, AnchoredConcreteWitness N σ) N (fun N ih => by
    rcases lt_trichotomy N 1 with hN | hN | hN
    · have h0N : N = 0 := by omega
      subst h0N
      exact ⟨fun _ => 0, anchoredConcreteWitness_zero⟩
    · subst hN
      exact ⟨fun _ => 0, anchoredConcreteWitness_one⟩
    · have h2 : 2 ≤ N := by omega
      obtain ⟨σe, σo, E, hE, he, ho, hslot0, hConcrete, hBad⟩ :=
        hstep N h2 (ih ((N + 1) / 2) (by omega)) (ih (N / 2) (by omega))
      exact ⟨slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE),
        anchoredConcreteWitness_of_evenPositionSet_badShuffle he ho hslot0 hConcrete hBad⟩)
  exact ⟨σ, hσ.1⟩

/-- Existential concrete-witness recursion with the minimal odd-difference merge
obligation. This is currently the closest formal target to the successful finite
searches: recursively choose concrete children and a merge word that meets deadlines
and kills odd-difference monotone 4-APs. -/
theorem finiteFeasible_of_child_anchoredConcreteWitnessOddDiffSafeEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, AnchoredConcreteWitness ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, AnchoredConcreteWitness (N / 2) σo) →
        ∃ σe σo : ℕ → ℕ, ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          AnchoredConcreteWitness ((N + 1) / 2) σe ∧
          AnchoredConcreteWitness (N / 2) σo ∧
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddDiffSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    FiniteFeasible twoMulAddSix := by
  intro N
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, AnchoredConcreteWitness N σ := by
    exact Nat.strongRecOn
      (motive := fun N => ∃ σ : ℕ → ℕ, AnchoredConcreteWitness N σ) N (fun N ih => by
    rcases lt_trichotomy N 1 with hN | hN | hN
    · have h0N : N = 0 := by omega
      subst h0N
      exact ⟨fun _ => 0, anchoredConcreteWitness_zero⟩
    · subst hN
      exact ⟨fun _ => 0, anchoredConcreteWitness_one⟩
    · have h2 : 2 ≤ N := by omega
      obtain ⟨σe, σo, E, hE, he, ho, hslot0, hConcrete, hOddDiff⟩ :=
        hstep N h2 (ih ((N + 1) / 2) (by omega)) (ih (N / 2) (by omega))
      exact ⟨slotMergeRank N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE),
        anchoredConcreteWitness_of_evenPositionSet_oddDiffSafe he ho hslot0 hConcrete
          hOddDiff⟩)
  exact ⟨σ, hσ.1⟩

/-- The empty witness satisfies the scale-tight deadline invariant. -/
theorem scaleBounded_zero : ScaleBounded 0 (fun _ => 0) := by
  intro v hv
  omega

/-- The singleton witness satisfies the scale-tight deadline invariant. -/
theorem scaleBounded_one : ScaleBounded 1 (fun _ => 0) := by
  intro v hv
  have hv0 : v = 0 := by omega
  subst hv0
  simp [scaleBound, scaleSlack]

/-- Concrete scale-tight pivot theorem. This specializes the abstract invariant `P` to
`ScaleBounded`: the recursive construction only has to choose the even-position set `E`
so that the resulting slots satisfy the scale-tight deadlines and split-safety. -/
theorem finiteFeasible_of_child_scaleBoundedEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness ScaleBounded ((N + 1) / 2) σe →
      CompatibleGoodWitness ScaleBounded (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          ScaleSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_compatibleEvenPositionSet
    (P := ScaleBounded) scaleBounded_zero scaleBounded_one
  intro N hN σe σo hσe hσo
  obtain ⟨E, hE, hScale, hSplit⟩ := hstep N hN σe σo hσe hσo
  refine ⟨E, hE, ?_, ?_, hSplit, ?_⟩
  · exact evenSlotPointwiseBudget_of_scaleSlotBound hScale
  · exact oddSlotPointwiseBudget_of_scaleSlotBound hScale
  · exact scaleBounded_slotMergeRank_of_scaleSlotBound hScale

/-- Anchored scale-tight version of the even-position-set target. This is the sharper
candidate after the `N = 10` search: keep value `0` first at every scale, and choose
the even-position set with first even slot equal to `0`. -/
theorem finiteFeasible_of_child_anchoredScaleBoundedEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness AnchoredScaleBounded ((N + 1) / 2) σe →
      CompatibleGoodWitness AnchoredScaleBounded (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          evenPositionSlot N E hE 0 = 0 ∧
          ScaleSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_compatibleEvenPositionSet
    (P := AnchoredScaleBounded)
  · exact ⟨scaleBounded_zero, rfl⟩
  · exact ⟨scaleBounded_one, rfl⟩
  · intro N hN σe σo hσe hσo
    obtain ⟨E, hE, hslot0, hScale, hSplit⟩ := hstep N hN σe σo hσe hσo
    refine ⟨E, hE, ?_, ?_, hSplit, ?_⟩
    · exact evenSlotPointwiseBudget_of_scaleSlotBound hScale
    · exact oddSlotPointwiseBudget_of_scaleSlotBound hScale
    · exact anchoredScaleBounded_slotMergeRank_of_scaleSlotBound hσe.2 hScale hslot0

/-- Budgeted good-merge constructor. To finish the recursive construction, it is enough
to build, from prepared children, a parent satisfying `GoodDyadicMergeStep` for some
nonnegative budget parameters. -/
theorem finiteFeasible_of_child_goodDyadicMergeStep
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      GoodWitness ((N + 1) / 2) σe →
      GoodWitness (N / 2) σo →
        ∃ Ae Ao Ce Co : ℕ, ∃ σ : ℕ → ℕ,
          GoodDyadicMergeStep Ae Ao Ce Co N σe σo σ) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_goodWitness
  intro N hN he ho
  obtain ⟨σe, hσe⟩ := he
  obtain ⟨σo, hσo⟩ := ho
  obtain ⟨Ae, Ao, Ce, Co, σ, hσ⟩ := hstep N hN σe σo hσe hσo
  exact ⟨σ, goodWitness_of_goodDyadicMergeStep hσe hσo hσ⟩

/-- Exact pointwise-budget merge constructor. This is the preferred proof target after
the numerical credit/lag analysis. -/
theorem finiteFeasible_of_child_exactGoodDyadicMergeStep
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      GoodWitness ((N + 1) / 2) σe →
      GoodWitness (N / 2) σo →
        ∃ σ : ℕ → ℕ, ExactGoodDyadicMergeStep N σe σo σ) :
    FiniteFeasible twoMulAddSix := by
  apply finiteFeasible_of_child_goodWitness
  intro N hN he ho
  obtain ⟨σe, hσe⟩ := he
  obtain ⟨σo, hσo⟩ := ho
  obtain ⟨σ, hσ⟩ := hstep N hN σe σo hσe hσo
  exact ⟨σ, goodWitness_of_exactGoodDyadicMergeStep hσe hσo hσ⟩

/-- A strong-recursion constructor for the merge-witness target. This is useful when a
candidate construction is most naturally presented as "build level `N` assuming all
smaller levels have already been built." -/
theorem finiteFeasible_of_strong_mergeWitness {f : ℕ → ℕ}
    (hstep : ∀ N : ℕ,
      (∀ M : ℕ, M < N → ∃ τ : ℕ → ℕ, MergeWitness f M τ) →
        ∃ σ : ℕ → ℕ, MergeWitness f N σ) :
    FiniteFeasible f :=
  finiteFeasible_of_mergeWitness (fun N => Nat.strongRecOn N hstep)

/-- Dyadic-recursion constructor for the merge-witness target. To prove `FiniteFeasible f`,
it is enough to build the parent witness at every `N ≥ 2` from witnesses for the two
parity children, whose sizes are `⌈N/2⌉` and `⌊N/2⌋`. This is the proof-theoretic
shape of the remaining #196 construction problem. -/
theorem finiteFeasible_of_child_mergeWitness {f : ℕ → ℕ}
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, MergeWitness f ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, MergeWitness f (N / 2) σo) →
        ∃ σ : ℕ → ℕ, MergeWitness f N σ) :
    FiniteFeasible f := by
  apply finiteFeasible_of_strong_mergeWitness
  intro N ih
  rcases lt_trichotomy N 1 with hN | hN | hN
  · have h0 : N = 0 := by omega
    subst h0
    exact ⟨fun _ => 0, mergeWitness_zero f⟩
  · subst hN
    exact ⟨fun _ => 0, mergeWitness_one f⟩
  · have h2 : 2 ≤ N := by omega
    exact hstep N h2
      (ih ((N + 1) / 2) (by omega))
      (ih (N / 2) (by omega))

/-- Stronger but construction-friendly dyadic-recursion constructor: it is enough to
build a flexible merge step from arbitrary child witnesses. If later evidence shows
that only specially prepared child witnesses can be merged, this theorem marks exactly
where an additional invariant should be threaded. -/
theorem finiteFeasible_of_child_dyadicMergeStep {f : ℕ → ℕ}
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      MergeWitness f ((N + 1) / 2) σe →
      MergeWitness f (N / 2) σo →
        ∃ σ : ℕ → ℕ, DyadicMergeStep f N σe σo σ) :
    FiniteFeasible f := by
  apply finiteFeasible_of_child_mergeWitness
  intro N hN he ho
  obtain ⟨σe, hσe⟩ := he
  obtain ⟨σo, hσo⟩ := ho
  obtain ⟨σ, hσ⟩ := hstep N hN σe σo hσe hσo
  exact ⟨σ, mergeWitness_of_dyadicMergeStep hσe hσo hσ⟩

end ConstructionTargets

/-! ### Finite segments: vdc order kills all finite obstructions.

The van der Corput order itself is not of order type `ω`, but any finite initial segment
can be ranked by counting its vdc-predecessors inside that segment. This gives a finite
4-AP-free order for every `N`. The compactness theorem below shows exactly what is still
missing for #196: the same finite witnesses must satisfy one pointwise bound `f`, uniformly
in `N`.
-/

open scoped Classical in
/-- The finite van der Corput rank of `v` inside `[0,N)`. -/
noncomputable def vdcFiniteRank (N v : ℕ) : ℕ :=
  ((Finset.range N).filter (fun w => VDC.vdcLt w v)).card

/-- Finite vdc rank is strictly monotone along `VDC.vdcLt`, as long as the lower
endpoint lies in the finite segment. -/
theorem vdcFiniteRank_lt_of_vdcLt {N v w : ℕ} (hv : v < N) (h : VDC.vdcLt v w) :
    vdcFiniteRank N v < vdcFiniteRank N w := by
  classical
  rw [vdcFiniteRank, vdcFiniteRank]
  apply Finset.card_lt_card
  have hsub : (Finset.range N).filter (fun u => VDC.vdcLt u v) ⊆
      (Finset.range N).filter (fun u => VDC.vdcLt u w) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, VDC.vdcLt_trans hx.2 h⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv, h⟩,
    fun hc => VDC.vdcLt_irrefl v (Finset.mem_filter.mp hc).2⟩

/-- Finite vdc rank is injective on `[0,N)`. -/
theorem vdcFiniteRank_injOn (N : ℕ) :
    Set.InjOn (vdcFiniteRank N) (Set.Iio N) := by
  intro v hv w hw hvw
  by_contra hne
  rcases VDC.vdcLt_total hne with h | h
  · exact absurd hvw (vdcFiniteRank_lt_of_vdcLt (Set.mem_Iio.mp hv) h).ne
  · exact absurd hvw.symm (vdcFiniteRank_lt_of_vdcLt (Set.mem_Iio.mp hw) h).ne

/-- Comparing finite vdc ranks recovers the underlying vdc comparison. -/
theorem vdcLt_of_vdcFiniteRank_lt {N v w : ℕ} (hw : w < N)
    (h : vdcFiniteRank N v < vdcFiniteRank N w) : VDC.vdcLt v w := by
  by_contra hnot
  rcases eq_or_ne v w with rfl | hne
  · exact (lt_irrefl _) h
  · rcases VDC.vdcLt_total hne with hvw | hwv
    · exact hnot hvw
    · exact (not_lt.mpr (vdcFiniteRank_lt_of_vdcLt hw hwv).le) h

/-- If a uniform finite-feasibility bound exists, then the forgetful finite-orderability
statement holds. The converse is false in exactly the compactness/order-type direction:
finite vdc ranks witness this theorem but do not provide one uniform bound. -/
theorem finiteOrderable4_of_finiteFeasible {f : ℕ → ℕ}
    (hf : FiniteFeasible f) : FiniteOrderable4 := by
  intro N
  obtain ⟨σ, hinj, _hbound, hfree⟩ := hf N
  exact ⟨σ, hinj, hfree⟩

/-- **Finite initial segments have no obstruction.** For every `N`, ranking `[0,N)` by
the van der Corput order gives an injective order with no monotone 4-term AP. Thus any
resolution of Erdős #196 must use the uniform `ω`-bound in `FiniteFeasible`, not merely
finite avoidability. -/
theorem finite_initial_segments_vdc_orderable : FiniteOrderable4 := by
  intro N
  refine ⟨vdcFiniteRank N, vdcFiniteRank_injOn N, ?_⟩
  rintro ⟨a, d, hd, h3, hmono⟩
  have ha : a < N := by omega
  have ha1 : a + d < N := by omega
  have ha2 : a + 2 * d < N := by omega
  have ha3 : a + 3 * d < N := by omega
  apply VDC.vdc_no_monotone_fourAP a d hd
  rcases hmono with ⟨h01, h12, h23⟩ | ⟨h32, h21, h10⟩
  · exact Or.inl
      ⟨vdcLt_of_vdcFiniteRank_lt ha1 h01,
       vdcLt_of_vdcFiniteRank_lt ha2 h12,
       vdcLt_of_vdcFiniteRank_lt ha3 h23⟩
  · exact Or.inr
      ⟨vdcLt_of_vdcFiniteRank_lt ha2 h32,
       vdcLt_of_vdcFiniteRank_lt ha1 h21,
       vdcLt_of_vdcFiniteRank_lt ha h10⟩

/-! ### Stage A: a global `σ : ℕ → ℕ` via König's lemma. -/

/-- Extend a partial assignment `g : Fin N → ℕ` to all of `ℕ` by `0` outside `[0,N)`. -/
def extend {N : ℕ} (g : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then g ⟨n, h⟩ else 0

theorem extend_apply {N : ℕ} (g : Fin N → ℕ) (n : ℕ) (h : n < N) :
    extend g n = g ⟨n, h⟩ := dif_pos h

/-- The level type for König's lemma at stage `N`: an injective rank assignment of the
initial segment `Fin N`, bounded pointwise by `f`, and free of monotone 4-APs. -/
def Level (f : ℕ → ℕ) (N : ℕ) : Type :=
  { g : Fin N → ℕ // Function.Injective g ∧ (∀ v : Fin N, g v ≤ f v.val) ∧
      ∀ a d : ℕ, 0 < d → a + 3 * d < N → ¬ Mono4 (extend g) a d }

instance instFiniteLevel (f : ℕ → ℕ) (N : ℕ) : Finite (Level f N) := by
  have hbase : Finite { g : Fin N → ℕ // ∀ v : Fin N, g v ≤ f v.val } := by
    apply Finite.of_injective
      (β := ∀ v : Fin N, Fin (f v.val + 1))
      (fun g v => ⟨g.val v, Nat.lt_succ_of_le (g.property v)⟩)
    intro g g' hgg'
    apply Subtype.ext
    funext v
    have := congrFun hgg' v
    simpa using congrArg Fin.val this
  -- `Level f N` is a subtype of the finite type `{ g // ∀ v, g v ≤ f v }`.
  apply Finite.of_injective
    (β := { g : Fin N → ℕ // ∀ v : Fin N, g v ≤ f v.val })
    (fun L => ⟨L.val, L.property.2.1⟩)
  intro L L' h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext h

/-- `Mono4` depends only on the values of `σ` at `a, a+d, a+2d, a+3d`. -/
theorem mono4_congr {σ τ : ℕ → ℕ} {a d : ℕ}
    (h0 : σ a = τ a) (h1 : σ (a + d) = τ (a + d))
    (h2 : σ (a + 2 * d) = τ (a + 2 * d)) (h3 : σ (a + 3 * d) = τ (a + 3 * d)) :
    Mono4 σ a d ↔ Mono4 τ a d := by
  unfold Mono4; rw [h0, h1, h2, h3]

/-- From a finite feasible witness at stage `N`, the level type `Level f N` is nonempty. -/
theorem nonempty_level_of_finiteFeasible (f : ℕ → ℕ) (h : FiniteFeasible f) (N : ℕ) :
    Nonempty (Level f N) := by
  obtain ⟨σ, hinj, hbound, hfree⟩ := h N
  refine ⟨⟨fun v => σ v.val, ?_, ?_, ?_⟩⟩
  · -- injective from `InjOn σ (Iio N)`
    intro v w hvw
    exact Fin.ext (hinj (Set.mem_Iio.mpr v.isLt) (Set.mem_Iio.mpr w.isLt) hvw)
  · -- pointwise bound
    intro v
    exact hbound v.val v.isLt
  · -- 4-AP-freeness transfers from `σ`
    intro a d hd h3 hmono
    refine hfree ⟨a, d, hd, h3, ?_⟩
    -- `extend g` agrees with `σ` on the four indices (all `< N`)
    have ha : a < N := by omega
    have had : a + d < N := by omega
    have ha2 : a + 2 * d < N := by omega
    have e0 : extend (fun v : Fin N => σ v.val) a = σ a := by
      rw [extend_apply _ _ ha]
    have e1 : extend (fun v : Fin N => σ v.val) (a + d) = σ (a + d) := by
      rw [extend_apply _ _ had]
    have e2 : extend (fun v : Fin N => σ v.val) (a + 2 * d) = σ (a + 2 * d) := by
      rw [extend_apply _ _ ha2]
    have e3 : extend (fun v : Fin N => σ v.val) (a + 3 * d) = σ (a + 3 * d) := by
      rw [extend_apply _ _ h3]
    exact (mono4_congr e0 e1 e2 e3).mp hmono

/-- The König projection: restrict a level at stage `j` to a level at stage `i ≤ j`,
by precomposing with `Fin.castLE`. -/
def levelProj (f : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) (L : Level f j) : Level f i := by
  refine ⟨fun v => L.val (Fin.castLE hij v), ?_, ?_, ?_⟩
  · -- injective: castLE injective, L.val injective
    intro v w hvw
    exact Fin.castLE_injective hij (L.property.1 hvw)
  · -- bound: castLE preserves underlying value
    intro v
    have hb := L.property.2.1 (Fin.castLE hij v)
    simpa using hb
  · -- 4-AP-freeness pulls back: the two extensions agree on `[0,i)`
    intro a d hd h3 hmono
    have h3j : a + 3 * d < j := lt_of_lt_of_le h3 hij
    refine L.property.2.2 a d hd h3j ?_
    -- agreement of extensions on the four indices (all `< i ≤ j`)
    have agree : ∀ n : ℕ, n < i →
        extend (fun v : Fin i => L.val (Fin.castLE hij v)) n = extend L.val n := by
      intro n hn
      rw [extend_apply _ _ hn, extend_apply _ _ (lt_of_lt_of_le hn hij)]
      rfl
    have e0 := agree a (by omega)
    have e1 := agree (a + d) (by omega)
    have e2 := agree (a + 2 * d) (by omega)
    have e3 := agree (a + 3 * d) h3
    exact (mono4_congr e0 e1 e2 e3).mp hmono

theorem levelProj_refl (f : ℕ → ℕ) {i : ℕ} (L : Level f i) :
    levelProj f (le_refl i) L = L := by
  apply Subtype.ext
  funext v
  rfl

theorem levelProj_trans (f : ℕ → ℕ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (L : Level f k) :
    levelProj f hij (levelProj f hjk L) = levelProj f (hij.trans hjk) L := by
  apply Subtype.ext
  funext v
  rfl

/-- **Stage A.** From finite feasibility, König's lemma threads the finite levels into a
single global rank assignment `σ : ℕ → ℕ`: injective, bounded by `f`, and free of all
monotone 4-APs (at every scale `N`). -/
theorem global_sigma (f : ℕ → ℕ) (h : FiniteFeasible f) :
    ∃ σ : ℕ → ℕ, Function.Injective σ ∧ (∀ v, σ v ≤ f v) ∧ ∀ N, ¬ HasMono4 σ N := by
  -- instances for König
  haveI : Finite (Level f 0) := instFiniteLevel f 0
  haveI : ∀ i, Nonempty (Level f i) := fun i => nonempty_level_of_finiteFeasible f h i
  -- apply König's infinity lemma
  obtain ⟨F, hF⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun i => Level f i)
    (π := fun {i j} hij L => levelProj f hij L)
    (fun {i} a => levelProj_refl f a)
    (fun {i j k} hij hjk a => levelProj_trans f hij hjk a)
    (fun i a => Set.toFinite _)
  -- the global rank assignment
  set σ : ℕ → ℕ := fun v => (F (v + 1)).val ⟨v, Nat.lt_succ_self v⟩ with hσ
  -- compatibility: for any window `j > v`, the level `F j` reports `σ v` at index `v`.
  have compat : ∀ v j : ℕ, ∀ hv : v < j, (F j).val ⟨v, hv⟩ = σ v := by
    intro v j hv
    have hle : v + 1 ≤ j := hv
    have hproj := hF hle
    -- `levelProj f hle (F j)` at `⟨v, _⟩` is `(F j).val ⟨v, hv⟩`
    have hc := congrArg (fun L => (L.val ⟨v, Nat.lt_succ_self v⟩)) hproj
    simpa [levelProj, σ] using hc
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- injectivity: compare inside a single level large enough to contain both indices
    intro u v huv
    set N := max u v + 1 with hN
    have hu : u < N := by omega
    have hv : v < N := by omega
    have eu : (F N).val ⟨u, hu⟩ = σ u := compat u N hu
    have ev : (F N).val ⟨v, hv⟩ = σ v := compat v N hv
    have : (F N).val ⟨u, hu⟩ = (F N).val ⟨v, hv⟩ := by rw [eu, ev, huv]
    have := (F N).property.1 this
    exact congrArg Fin.val this
  · -- pointwise bound
    intro v
    have hb := (F (v + 1)).property.2.1 ⟨v, Nat.lt_succ_self v⟩
    simpa [σ] using hb
  · -- 4-AP-freeness at every scale
    intro N hN
    obtain ⟨a, d, hd, h3, hmono⟩ := hN
    -- work inside level `F N`; all four indices are `< N`
    refine (F N).property.2.2 a d hd h3 ?_
    have agree : ∀ n : ℕ, n < N → extend (F N).val n = σ n := by
      intro n hn
      rw [extend_apply _ _ hn]
      exact compat n N hn
    have e0 := agree a (by omega)
    have e1 := agree (a + d) (by omega)
    have e2 := agree (a + 2 * d) (by omega)
    have e3 := agree (a + 3 * d) h3
    exact (mono4_congr e0 e1 e2 e3).mpr hmono

/-! ### Stage B: compress `σ` to a genuine permutation of order type ω.

Given the global `σ` (injective, free of all monotone 4-APs), the σ-order
`u ≺ v ↔ σ u < σ v` is a well-order of type ω: every value has only finitely many
σ-predecessors (they inject into `Set.Iio (σ v)`). The **rank** `ρ v := |{u | σ u < σ v}|`
is the order-isomorphism to ℕ. We show `ρ` is bijective and that the inverse permutation
inherits 4-AP-freeness. -/

/-- The set of σ-predecessors of `v` is finite: `σ` injects it into `Set.Iio (σ v)`. -/
theorem finite_sigmaLt {σ : ℕ → ℕ} (hinj : Function.Injective σ) (v : ℕ) :
    {u | σ u < σ v}.Finite := by
  apply Set.Finite.ofFinset (Finset.range (σ v) |>.preimage σ (hinj.injOn))
  intro u
  simp only [Finset.mem_preimage, Finset.mem_range, Set.mem_setOf_eq]

/-- The **σ-rank** of `v`: the number of values strictly below `v` in the σ-order. -/
noncomputable def rank (σ : ℕ → ℕ) (v : ℕ) : ℕ := {u | σ u < σ v}.ncard

/-- **Rank is strictly monotone in the σ-order.** If `σ u < σ v` then `rank σ u < rank σ v`,
because the σ-predecessors of `u` form a proper subset of those of `v` (the latter also
contains `u` itself). -/
theorem rank_lt_rank {σ : ℕ → ℕ} (hinj : Function.Injective σ) {u v : ℕ}
    (huv : σ u < σ v) : rank σ u < rank σ v := by
  have hsub : {w | σ w < σ u} ⊆ {w | σ w < σ v} := fun w hw =>
    lt_trans hw huv
  have hu_not : u ∉ {w | σ w < σ u} := by simp [Set.mem_setOf_eq]
  have hu_in : u ∈ {w | σ w < σ v} := huv
  have hssub : {w | σ w < σ u} ⊂ {w | σ w < σ v} :=
    ⟨hsub, fun hcon => hu_not (hcon hu_in)⟩
  exact Set.ncard_lt_ncard hssub (finite_sigmaLt hinj v)

/-- **Rank is injective:** distinct values have distinct σ-values (σ injective), and the
σ-order is total, so their ranks differ by `rank_lt_rank`. -/
theorem rank_injective {σ : ℕ → ℕ} (hinj : Function.Injective σ) :
    Function.Injective (rank σ) := by
  intro u v huv
  rcases lt_trichotomy (σ u) (σ v) with h | h | h
  · exact absurd huv (rank_lt_rank hinj h).ne
  · exact hinj h
  · exact absurd huv.symm (rank_lt_rank hinj h).ne

/-- **The range of `rank` is downward closed.** For any `m < rank σ v`, there is a value
`u` with `rank σ u = m`. Indeed `rank` maps the σ-predecessors of `v` injectively into
`Set.Iio (rank σ v)`, and since `|{u | σ u < σ v}| = rank σ v = |Iio (rank σ v)|`, this map
is onto the initial segment. -/
theorem rank_range_downward {σ : ℕ → ℕ} (hinj : Function.Injective σ) {v m : ℕ}
    (hm : m < rank σ v) : ∃ u, rank σ u = m := by
  have hfin : {u | σ u < σ v}.Finite := finite_sigmaLt hinj v
  -- `rank` maps σ-predecessors of `v` into `Iio (rank σ v)`, injectively, with equal card.
  have hmaps : ∀ u ∈ {u | σ u < σ v}, rank σ u ∈ Set.Iio (rank σ v) := by
    intro u hu; exact rank_lt_rank hinj hu
  have hinjon : ∀ (a₁ a₂ : ℕ), a₁ ∈ {u | σ u < σ v} → a₂ ∈ {u | σ u < σ v} →
      rank σ a₁ = rank σ a₂ → a₁ = a₂ :=
    fun a₁ a₂ _ _ heq => rank_injective hinj heq
  -- card of the target initial segment equals card of the predecessor set (= rank σ v)
  have hcard : (Set.Iio (rank σ v)).ncard ≤ ({u | σ u < σ v}).ncard := by
    rw [Set.ncard_Iio_nat]; exact le_of_eq rfl
  -- surjectivity onto the initial segment yields a preimage of `m`
  have htfin : (Set.Iio (rank σ v)).Finite := Set.finite_Iio _
  obtain ⟨u, _, hu⟩ := Set.surj_on_of_inj_on_of_ncard_le
    (s := {u | σ u < σ v}) (t := Set.Iio (rank σ v))
    (fun a _ => rank σ a) hmaps hinjon hcard htfin m (Set.mem_Iio.mpr hm)
  exact ⟨u, hu.symm⟩

/-- **Rank is surjective.** Its range is infinite (rank is injective and ℕ is infinite)
hence unbounded, and downward closed (`rank_range_downward`); an unbounded downward-closed
subset of ℕ is everything. -/
theorem rank_surjective {σ : ℕ → ℕ} (hinj : Function.Injective σ) :
    Function.Surjective (rank σ) := by
  intro n
  -- the range of `rank σ` is infinite
  have hrange_inf : (Set.range (rank σ)).Infinite :=
    Set.infinite_range_of_injective (rank_injective hinj)
  -- hence it has an element `> n`
  obtain ⟨b, hb_mem, hb_gt⟩ := hrange_inf.exists_gt n
  obtain ⟨v, hv⟩ := hb_mem
  -- `n < b = rank σ v`, so downward closure gives a preimage of `n`
  have : n < rank σ v := by rwa [hv]
  exact rank_range_downward hinj this

/-- **The compactness bridge for Erdős #196.** If, for some uniform bound `f`, every
initial segment `[0,N)` admits an injective 4-AP-free order with `σ v ≤ f v`, then ℕ
admits a permutation avoiding all monotone 4-APs. -/
theorem erdos196Avoidable_of_finiteFeasible (f : ℕ → ℕ) (h : FiniteFeasible f) :
    Erdos196Avoidable := by
  -- Stage A: the global rank assignment.
  obtain ⟨σ, hinj, _hbound, hfree⟩ := global_sigma f h
  -- The σ-order and the rank order coincide.
  have rank_iff : ∀ u v : ℕ, rank σ u < rank σ v ↔ σ u < σ v := by
    intro u v
    constructor
    · intro hr
      rcases lt_trichotomy (σ u) (σ v) with h' | h' | h'
      · exact h'
      · exact absurd (congrArg (rank σ) (hinj h')) hr.ne
      · exact absurd (rank_lt_rank hinj h') (not_lt.mpr hr.le)
    · exact rank_lt_rank hinj
  -- The permutation: value ↦ σ-rank.
  set e : ℕ ≃ ℕ := Equiv.ofBijective (rank σ) ⟨rank_injective hinj, rank_surjective hinj⟩
    with he
  -- `rank σ (e.symm n) = n` for all `n` (the inverse identity).
  have hrank_symm : ∀ n, rank σ (e.symm n) = n := by
    intro n
    have : e (e.symm n) = n := e.apply_symm_apply n
    simpa [he, Equiv.ofBijective] using this
  -- Use `e.symm` as the position → value permutation.
  refine ⟨e.symm, ?_⟩
  intro hmono
  obtain ⟨p, hp, a, d, hAP⟩ := hmono
  -- The four AP values, indexed by the positions.
  set v₀ := e.symm (p 0) with hv0
  set v₁ := e.symm (p 1) with hv1
  set v₂ := e.symm (p 2) with hv2
  set v₃ := e.symm (p 3) with hv3
  -- σ-values are strictly increasing along the (strictly increasing) positions:
  -- positions = ranks, and ranks-order = σ-order.
  have hσ01 : σ v₀ < σ v₁ := by
    rw [← rank_iff]; rw [hv0, hv1, hrank_symm, hrank_symm]; exact hp (by norm_num)
  have hσ12 : σ v₁ < σ v₂ := by
    rw [← rank_iff]; rw [hv1, hv2, hrank_symm, hrank_symm]; exact hp (by norm_num)
  have hσ23 : σ v₂ < σ v₃ := by
    rw [← rank_iff]; rw [hv2, hv3, hrank_symm, hrank_symm]; exact hp (by norm_num)
  -- The integer AP relations at j = 0,1,2,3.
  have hA0 : (v₀ : ℤ) = a := by have := hAP 0 (by norm_num); simpa using this
  have hA1 : (v₁ : ℤ) = a + d := by have := hAP 1 (by norm_num); simpa using this
  have hA2 : (v₂ : ℤ) = a + 2 * d := by
    have := hAP 2 (by norm_num); simpa using this
  have hA3 : (v₃ : ℤ) = a + 3 * d := by
    have := hAP 3 (by norm_num); simpa using this
  -- The four values are distinct (σ-values are distinct), so `d ≠ 0`.
  have hne01 : v₀ ≠ v₁ := fun heq => absurd (heq ▸ hσ01) (lt_irrefl _)
  have hd0 : d ≠ 0 := by
    intro hd; apply hne01
    have : (v₀ : ℤ) = (v₁ : ℤ) := by rw [hA0, hA1, hd]; ring
    exact Nat.cast_injective this
  rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
  · -- `d < 0`: the AP decreases; base it at `v₃` with step `δ = -d`.
    set δ : ℕ := (-d).toNat with hδ
    have hδpos : 0 < δ := by
      rw [hδ]; omega
    have hδcast : (δ : ℤ) = -d := by rw [hδ]; omega
    -- nat identities `v₂ = v₃ + δ`, `v₁ = v₃ + 2δ`, `v₀ = v₃ + 3δ`
    have e2 : v₂ = v₃ + δ := by
      have : (v₂ : ℤ) = (v₃ : ℤ) + δ := by rw [hA2, hA3, hδcast]; ring
      exact_mod_cast this
    have e1 : v₁ = v₃ + 2 * δ := by
      have : (v₁ : ℤ) = (v₃ : ℤ) + 2 * δ := by rw [hA1, hA3, hδcast]; ring
      exact_mod_cast this
    have e0 : v₀ = v₃ + 3 * δ := by
      have : (v₀ : ℤ) = (v₃ : ℤ) + 3 * δ := by rw [hA0, hA3, hδcast]; ring
      exact_mod_cast this
    -- exhibit a decreasing σ-monotone 4-AP based at `v₃`
    refine hfree (v₃ + 3 * δ + 1) ⟨v₃, δ, hδpos, by omega, Or.inr ?_⟩
    rw [← e0, ← e1, ← e2]
    exact ⟨hσ01, hσ12, hσ23⟩
  · -- `d > 0`: the AP increases; base it at `v₀` with step `δ = d`.
    set δ : ℕ := d.toNat with hδ
    have hδpos : 0 < δ := by rw [hδ]; omega
    have hδcast : (δ : ℤ) = d := by rw [hδ]; omega
    have e1 : v₁ = v₀ + δ := by
      have : (v₁ : ℤ) = (v₀ : ℤ) + δ := by rw [hA1, hA0, hδcast]
      exact_mod_cast this
    have e2 : v₂ = v₀ + 2 * δ := by
      have : (v₂ : ℤ) = (v₀ : ℤ) + 2 * δ := by rw [hA2, hA0, hδcast]
      exact_mod_cast this
    have e3 : v₃ = v₀ + 3 * δ := by
      have : (v₃ : ℤ) = (v₀ : ℤ) + 3 * δ := by rw [hA3, hA0, hδcast]
      exact_mod_cast this
    -- exhibit an increasing σ-monotone 4-AP based at `v₀`
    refine hfree (v₀ + 3 * δ + 1) ⟨v₀, δ, hδpos, by omega, Or.inl ?_⟩
    rw [← e1, ← e2, ← e3]
    exact ⟨hσ01, hσ12, hσ23⟩

/-- Packaged form: it suffices to exhibit *some* uniform bound under which all finite
initial segments are 4-AP-free-orderable. -/
theorem erdos196Avoidable_of_exists_finiteFeasible
    (h : ∃ f : ℕ → ℕ, FiniteFeasible f) : Erdos196Avoidable := by
  obtain ⟨f, hf⟩ := h
  exact erdos196Avoidable_of_finiteFeasible f hf

section ConstructionTargets
/-! ## Construction-side `Erdos196Avoidable` wrappers (exploratory; conditional on the merge step)

Each theorem below composes `erdos196Avoidable_of_finiteFeasible` with one construction-side
reduction; every one carries an undischarged `hstep` / `FiniteFeasible` hypothesis, and none is
used by `exists_finiteFeasible_iff_avoidable` or any unconditional result. These are the
`Erdos196Avoidable`-level entry points of the same exploratory tower. -/

/-- The current concrete construction target suggested by finite SAT searches: proving
`FiniteFeasible (fun v => 2 * v + 6)` would immediately give a 4-AP-avoiding
permutation of `ℕ`, hence a negative answer to Erdős #196. -/
theorem erdos196Avoidable_of_two_mul_add_six
    (h : FiniteFeasible (fun v => 2 * v + 6)) : Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible (fun v => 2 * v + 6) h

/-- Construction-facing version of the #196 compactness bridge: bounded parity-merge
witnesses at every finite level produce a 4-AP-avoiding permutation of `ℕ`. -/
theorem erdos196Avoidable_of_mergeWitness {f : ℕ → ℕ}
    (h : ∀ N : ℕ, ∃ σ : ℕ → ℕ, MergeWitness f N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible f (finiteFeasible_of_mergeWitness h)

/-- The sharp concrete target from the SAT search in merge-witness form. Proving the
hypothesis would take down Erdős #196 in the negative direction. -/
theorem erdos196Avoidable_of_two_mul_add_six_mergeWitness
    (h : ∀ N : ℕ, ∃ σ : ℕ → ℕ, MergeWitness (fun v => 2 * v + 6) N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_mergeWitness h

/-- Dyadic-recursive construction bridge: if every nontrivial finite level can be
merged from its two parity-child witnesses, then a 4-AP-avoiding permutation of `ℕ`
exists. -/
theorem erdos196Avoidable_of_child_mergeWitness {f : ℕ → ℕ}
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, MergeWitness f ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, MergeWitness f (N / 2) σo) →
        ∃ σ : ℕ → ℕ, MergeWitness f N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible f (finiteFeasible_of_child_mergeWitness hstep)

/-- Concrete #196 attack target in recursive merge form. Proving this single step for
the bound `σ v ≤ 2v+6` would refute `Erdos196`. -/
theorem erdos196Avoidable_of_two_mul_add_six_child_mergeWitness
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, MergeWitness (fun v => 2 * v + 6) ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, MergeWitness (fun v => 2 * v + 6) (N / 2) σo) →
        ∃ σ : ℕ → ℕ, MergeWitness (fun v => 2 * v + 6) N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_child_mergeWitness hstep

/-- Flexible-merge version of the recursive construction bridge. -/
theorem erdos196Avoidable_of_child_dyadicMergeStep {f : ℕ → ℕ}
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      MergeWitness f ((N + 1) / 2) σe →
      MergeWitness f (N / 2) σo →
        ∃ σ : ℕ → ℕ, DyadicMergeStep f N σe σo σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible f (finiteFeasible_of_child_dyadicMergeStep hstep)

/-- Concrete flexible-merge target for the SAT-supported bound `σ v ≤ 2v+6`. -/
theorem erdos196Avoidable_of_two_mul_add_six_child_dyadicMergeStep
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      MergeWitness (fun v => 2 * v + 6) ((N + 1) / 2) σe →
      MergeWitness (fun v => 2 * v + 6) (N / 2) σo →
        ∃ σ : ℕ → ℕ, DyadicMergeStep (fun v => 2 * v + 6) N σe σo σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_child_dyadicMergeStep hstep

/-- Prepared witnesses at every finite level produce a 4-AP-avoiding permutation of
`ℕ`. -/
theorem erdos196Avoidable_of_goodWitness
    (h : ∀ N : ℕ, ∃ σ : ℕ → ℕ, GoodWitness N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix (finiteFeasible_of_goodWitness h)

/-- Main proof target in prepared-witness form: if the split-safe prepared invariant
closes under the dyadic child merge, then Erdős #196 has a negative answer. -/
theorem erdos196Avoidable_of_child_goodWitness
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, GoodWitness ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, GoodWitness (N / 2) σo) →
        ∃ σ : ℕ → ℕ, GoodWitness N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_goodWitness hstep)

/-- Pivot target with an extra invariant `P`: it is enough to build a recursively
compatible family of prepared witnesses, not to merge arbitrary prepared children. -/
theorem erdos196Avoidable_of_child_compatibleGoodWitness
    {P : ℕ → (ℕ → ℕ) → Prop}
    (h0 : P 0 (fun _ => 0))
    (h1 : P 1 (fun _ => 0))
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, CompatibleGoodWitness P ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, CompatibleGoodWitness P (N / 2) σo) →
        ∃ σ : ℕ → ℕ, CompatibleGoodWitness P N σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_compatibleGoodWitness h0 h1 hstep)

/-- Slot-merge form of the pivot target. The remaining mathematical task is to find an
invariant `P` and a deadline-aware slot construction preserving `P`. -/
theorem erdos196Avoidable_of_child_compatibleSlotMerge
    {P : ℕ → (ℕ → ℕ) → Prop}
    (h0 : P 0 (fun _ => 0))
    (h1 : P 1 (fun _ => 0))
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness P ((N + 1) / 2) σe →
      CompatibleGoodWitness P (N / 2) σo →
        ∃ evenSlot oddSlot : ℕ → ℕ,
          SlotMergeCompatible N σe σo evenSlot oddSlot ∧
          P N (slotMergeRank N σe σo evenSlot oddSlot)) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_compatibleSlotMerge h0 h1 hstep)

/-- Even-position-set form of the pivot target. This is the most concrete current
route: find an invariant `P` and, for compatible children, choose the finite set of
parent positions occupied by the even stream. -/
theorem erdos196Avoidable_of_child_compatibleEvenPositionSet
    {P : ℕ → (ℕ → ℕ) → Prop}
    (h0 : P 0 (fun _ => 0))
    (h1 : P 1 (fun _ => 0))
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness P ((N + 1) / 2) σe →
      CompatibleGoodWitness P (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          EvenSlotPointwiseBudget N σe (evenPositionSlot N E hE) ∧
          OddSlotPointwiseBudget N σo (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N ∧
          P N (slotMergeRank N σe σo (evenPositionSlot N E hE)
            (oddPositionSlot N E hE))) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_compatibleEvenPositionSet h0 h1 hstep)

/-- Anchored concrete version of the even-position-set target. This is weaker than the
scale-tight target and matches the original `2v+6` construction budget directly. -/
theorem erdos196Avoidable_of_child_anchoredConcreteEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness Anchored ((N + 1) / 2) σe →
      CompatibleGoodWitness Anchored (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_anchoredConcreteEvenPositionSet hstep)

/-- Bad-shuffle form of the anchored concrete construction target. Proving this local
slot theorem would finish the negative direction of Erdős #196. -/
theorem erdos196Avoidable_of_child_anchoredConcreteBadShuffleEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness Anchored ((N + 1) / 2) σe →
      CompatibleGoodWitness Anchored (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          BadShuffleAvoiding
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_anchoredConcreteBadShuffleEvenPositionSet hstep)

/-- Existential concrete-witness version of the bad-shuffle construction target. This
is the weakest current recursive socket: prove that some anchored concrete children can
be merged at each scale with concrete deadlines and bad-shuffle avoidance, and #196 is
resolved in the avoidable direction. -/
theorem erdos196Avoidable_of_child_anchoredConcreteWitnessBadShuffleEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, AnchoredConcreteWitness ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, AnchoredConcreteWitness (N / 2) σo) →
        ∃ σe σo : ℕ → ℕ, ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          AnchoredConcreteWitness ((N + 1) / 2) σe ∧
          AnchoredConcreteWitness (N / 2) σo ∧
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          BadShuffleAvoiding
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_anchoredConcreteWitnessBadShuffleEvenPositionSet hstep)

/-- Minimal odd-difference version of the existential concrete construction target. This
is weaker than the bad-shuffle target and is the best current formal landing point for
the direct recursive construction. -/
theorem erdos196Avoidable_of_child_anchoredConcreteWitnessOddDiffSafeEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N →
      (∃ σe : ℕ → ℕ, AnchoredConcreteWitness ((N + 1) / 2) σe) →
      (∃ σo : ℕ → ℕ, AnchoredConcreteWitness (N / 2) σo) →
        ∃ σe σo : ℕ → ℕ, ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          AnchoredConcreteWitness ((N + 1) / 2) σe ∧
          AnchoredConcreteWitness (N / 2) σo ∧
          evenPositionSlot N E hE 0 = 0 ∧
          ConcreteSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddDiffSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_anchoredConcreteWitnessOddDiffSafeEvenPositionSet hstep)

/-- Concrete scale-tight version of the even-position-set target. This is the current
deadline-aware conjectural construction theorem: choose the finite set of even parent
positions so the slot merge satisfies `scaleBound` and split-safety. -/
theorem erdos196Avoidable_of_child_scaleBoundedEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness ScaleBounded ((N + 1) / 2) σe →
      CompatibleGoodWitness ScaleBounded (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          ScaleSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_scaleBoundedEvenPositionSet hstep)

/-- Anchored scale-tight version of the concrete target. This incorporates the small
search signal that keeping value `0` first removes the `N = 10` bad child-pair
obstruction. -/
theorem erdos196Avoidable_of_child_anchoredScaleBoundedEvenPositionSet
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      CompatibleGoodWitness AnchoredScaleBounded ((N + 1) / 2) σe →
      CompatibleGoodWitness AnchoredScaleBounded (N / 2) σo →
        ∃ E : Finset (Fin N), ∃ hE : E.card = (N + 1) / 2,
          evenPositionSlot N E hE 0 = 0 ∧
          ScaleSlotBound N σe σo (evenPositionSlot N E hE) (oddPositionSlot N E hE) ∧
          OddAPSplitSafe
            (slotMergeRank N σe σo (evenPositionSlot N E hE)
              (oddPositionSlot N E hE)) N) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_anchoredScaleBoundedEvenPositionSet hstep)

/-- Main attack target with the lag-budgeted prepared merge exposed explicitly. Build a
`GoodDyadicMergeStep` from any two prepared children, and the compactness bridge produces
a 4-AP-avoiding permutation of `ℕ`. -/
theorem erdos196Avoidable_of_child_goodDyadicMergeStep
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      GoodWitness ((N + 1) / 2) σe →
      GoodWitness (N / 2) σo →
        ∃ Ae Ao Ce Co : ℕ, ∃ σ : ℕ → ℕ,
          GoodDyadicMergeStep Ae Ao Ce Co N σe σo σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_goodDyadicMergeStep hstep)

/-- Main attack target in its sharper pointwise-budget form. Build an
`ExactGoodDyadicMergeStep` from any two prepared children, and the compactness bridge
produces a 4-AP-avoiding permutation of `ℕ`. -/
theorem erdos196Avoidable_of_child_exactGoodDyadicMergeStep
    (hstep : ∀ N : ℕ, 2 ≤ N → ∀ σe σo : ℕ → ℕ,
      GoodWitness ((N + 1) / 2) σe →
      GoodWitness (N / 2) σo →
        ∃ σ : ℕ → ℕ, ExactGoodDyadicMergeStep N σe σo σ) :
    Erdos196Avoidable :=
  erdos196Avoidable_of_finiteFeasible twoMulAddSix
    (finiteFeasible_of_child_exactGoodDyadicMergeStep hstep)

end ConstructionTargets

/-! ### The reverse direction: the reduction is tight.

If a 4-AP-avoiding permutation `g` exists, then `f := g.symm` (value ↦ position) is a
uniform displacement bound witnessing `FiniteFeasible`: each initial segment `[0,N)` is
ordered by `g.symm` itself, which is injective, meets the bound with equality, and is
4-AP-free because `g` is. Hence `∃ f, FiniteFeasible f` is an **exact** finitary
restatement of `Erdos196Avoidable` — there is no slack between the finitary search and
the genuine problem. -/

/-- Four positions `q0 < q1 < q2 < q3` whose `g`-values form an arithmetic progression
constitute a monotone 4-AP of the permutation `g`. (The increasing/decreasing sign of the
AP is carried by the common difference `d'`.) -/
theorem hasMonotoneAP_four_of_positions {g : ℕ ≃ ℕ} {q0 q1 q2 q3 : ℕ}
    (h01 : q0 < q1) (h12 : q1 < q2) (h23 : q2 < q3)
    {a' d' : ℤ} (hv0 : (g q0 : ℤ) = a') (hv1 : (g q1 : ℤ) = a' + d')
    (hv2 : (g q2 : ℤ) = a' + 2 * d') (hv3 : (g q3 : ℤ) = a' + 3 * d') :
    HasMonotoneAP (fun n => (g n : ℕ)) 4 := by
  refine ⟨fun j => match j with | 0 => q0 | 1 => q1 | 2 => q2 | (n + 3) => q3 + n,
          ?_, a', d', ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact h01
    | 1 => exact h12
    | 2 => simpa using h23
    | (n + 3) => simp only; omega
  · intro j hj
    interval_cases j
    · simpa using hv0
    · simpa using hv1
    · simpa using hv2
    · simpa using hv3

/-- **Reverse-bridge core.** If `g` avoids all monotone 4-APs then its inverse `g.symm`
(value ↦ position) has no monotone 4-AP below any `N`. Factored out so the same fact feeds
both the finite-feasibility witness and the single-order `AvoidV2` characterisation. -/
theorem not_hasMono4_symm_of_avoiding {g : ℕ ≃ ℕ}
    (hg : ¬ HasMonotoneAP (fun n => (g n : ℕ)) 4) (N : ℕ) :
    ¬ HasMono4 (g.symm : ℕ → ℕ) N := by
  rintro ⟨a, d, _hd, _h3, hcase⟩
  apply hg
  rcases hcase with ⟨H01, H12, H23⟩ | ⟨H01, H12, H23⟩
  · -- increasing AP `a, a+d, a+2d, a+3d`, positions ascending
    exact hasMonotoneAP_four_of_positions H01 H12 H23
      (a' := (a : ℤ)) (d' := (d : ℤ))
      (by rw [Equiv.apply_symm_apply])
      (by rw [Equiv.apply_symm_apply]; push_cast; ring)
      (by rw [Equiv.apply_symm_apply]; push_cast; ring)
      (by rw [Equiv.apply_symm_apply]; push_cast; ring)
  · -- decreasing AP: re-base at `a+3d` with step `-d` so positions ascend
    exact hasMonotoneAP_four_of_positions H01 H12 H23
      (a' := (a : ℤ) + 3 * d) (d' := -(d : ℤ))
      (by rw [Equiv.apply_symm_apply]; push_cast; ring)
      (by rw [Equiv.apply_symm_apply]; push_cast; ring)
      (by rw [Equiv.apply_symm_apply]; push_cast; ring)
      (by rw [Equiv.apply_symm_apply]; ring)

/-- **Reverse bridge.** A 4-AP-avoiding permutation of ℕ yields a uniform bound `f` (namely
`g.symm`) under which every initial segment is feasible. -/
theorem exists_finiteFeasible_of_erdos196Avoidable (h : Erdos196Avoidable) :
    ∃ f : ℕ → ℕ, FiniteFeasible f := by
  obtain ⟨g, hg⟩ := h
  exact ⟨(g.symm : ℕ → ℕ), fun N => ⟨(g.symm : ℕ → ℕ),
    (fun u _ v _ huv => g.symm.injective huv), (fun v _ => le_refl _),
    not_hasMono4_symm_of_avoiding hg N⟩⟩

/-- **The finitary characterisation of Erdős #196.** A permutation of ℕ avoiding all
monotone 4-term APs exists **iff** there is a uniform displacement bound `f` under which
every initial segment `[0,N)` admits an injective 4-AP-free order bounded by `f`. The
forward direction is König + rank-compression (`erdos196Avoidable_of_finiteFeasible`); the
reverse takes `f = g.symm`. This pins the open content of #196 as a purely finitary search
for a single uniform bound. -/
theorem exists_finiteFeasible_iff_avoidable :
    (∃ f : ℕ → ℕ, FiniteFeasible f) ↔ Erdos196Avoidable :=
  ⟨erdos196Avoidable_of_exists_finiteFeasible, exists_finiteFeasible_of_erdos196Avoidable⟩

/-- The obstruction-side version of the finitary characterisation: Erdős #196 is true
exactly when no uniform finite-feasibility bound exists. Thus an unconditional theorem
`∀ f, ¬ FiniteFeasible f` would be a full resolution of #196, not merely an auxiliary
finite obstruction. -/
theorem erdos196_iff_forall_not_finiteFeasible :
    Erdos196 ↔ ∀ f : ℕ → ℕ, ¬ FiniteFeasible f := by
  rw [← not_exists, exists_finiteFeasible_iff_avoidable, erdos196Avoidable_iff_not_erdos196]
  exact not_not.symm

/-! ### A forced necessary condition: unbounded displacement (the drift lemma).

The uniform bound `f` sought by the bridge cannot stay close to the identity. If the order's
displacement `|σ v − v|` is bounded by a constant `C`, then every AP of common difference
`d > 2 C` is placed in strictly increasing position order (each term moves by less than half a
step), producing arbitrarily long monotone APs. So a 4-AP avoider must **drift** — its bound
satisfies `f v − v → ∞` — while still keeping each value at a finite position (order type ω).
That tension is exactly what a #196 construction has to resolve, and it is why the bound `f`
cannot be anything as simple as `f = id`. -/

/-- If `g.symm` (value ↦ position) has displacement bounded by `C`, then `g` has a monotone
4-AP: the AP `0, d, 2d, 3d` with `d = 2 C + 1` has strictly ascending positions, because each
term's position is within `C` of its value and the gap `d` exceeds `2 C`. The four ascending
positions feed `hasMonotoneAP_four_of_positions`. -/
theorem hasMonotoneAP_four_of_bounded_displacement (g : ℕ ≃ ℕ) (C : ℕ)
    (hbd : ∀ v : ℕ, ((g.symm v : ℤ) - v).natAbs ≤ C) :
    HasMonotoneAP (fun n => (g n : ℕ)) 4 := by
  set d : ℕ := 2 * C + 1 with hd
  -- Two-sided integer bounds `v - C ≤ σ v ≤ v + C` from the displacement bound.
  have hbnd : ∀ v : ℕ, (v : ℤ) - C ≤ (g.symm v : ℤ) ∧ (g.symm v : ℤ) ≤ (v : ℤ) + C := by
    intro v
    have h : |((g.symm v : ℤ) - v)| ≤ (C : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hbd v
    have hpair := abs_le.mp h
    exact ⟨by linarith [hpair.1], by linarith [hpair.2]⟩
  have h01 : g.symm 0 < g.symm d := by
    have a0 := (hbnd 0).2; have ad := (hbnd d).1; omega
  have h12 : g.symm d < g.symm (2 * d) := by
    have a1 := (hbnd d).2; have a2 := (hbnd (2 * d)).1; omega
  have h23 : g.symm (2 * d) < g.symm (3 * d) := by
    have a2 := (hbnd (2 * d)).2; have a3 := (hbnd (3 * d)).1; omega
  exact hasMonotoneAP_four_of_positions h01 h12 h23
    (a' := 0) (d' := (d : ℤ))
    (by rw [Equiv.apply_symm_apply]; norm_num)
    (by rw [Equiv.apply_symm_apply]; ring)
    (by rw [Equiv.apply_symm_apply]; push_cast; ring)
    (by rw [Equiv.apply_symm_apply]; push_cast; ring)

/-- **Drift is forced (Erdős #196).** Every permutation of ℕ avoiding all monotone 4-APs has
unbounded displacement: for each `C` some value lies more than `C` from its position. Combined
with the compactness bridge, the witnessing bound `f` must drift (`f v − v` unbounded) yet keep
every value at a finite position — the precise, simultaneous demand a #196 construction faces. -/
theorem unbounded_displacement_of_avoiding (g : ℕ ≃ ℕ)
    (hg : ¬ HasMonotoneAP (fun n => (g n : ℕ)) 4) (C : ℕ) :
    ∃ v : ℕ, C < ((g.symm v : ℤ) - v).natAbs := by
  by_contra h
  exact hg (hasMonotoneAP_four_of_bounded_displacement g C
    (fun v => not_lt.mp (fun hlt => h ⟨v, hlt⟩)))

end PermutationMonotoneAP
