/- 
# Erdős Problem 156: Small Maximal Sidon Sets

Erdős, Sárközy, and Sós asked whether there exists a maximal Sidon subset of
`{1, ..., N}` of size `O(N^{1/3})`.

We package the problem in a finite form convenient for counting arguments:
instead of using asymptotic notation directly, we ask for a uniform constant
`C` such that `|A|^3 ≤ C N`.

Reference: https://www.erdosproblems.com/156
-/
import Erdos.SidonSumsets.Statement

namespace MaximalSidonSets

open SidonSumsets

/-- The finite interval `{1, ..., N}`. -/
def ground (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- A finite Sidon set, viewed through its coercion to a set. -/
def IsSidonFinset (A : Finset ℕ) : Prop :=
  IsSidon (A : Set ℕ)

/-- A finite Sidon set contained in `{1, ..., N}`. -/
def SidonInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  IsSidonFinset A ∧ ∀ a ∈ A, a ∈ ground N

/-- Maximality among Sidon subsets of `{1, ..., N}`. -/
def IsMaximalSidonInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  SidonInInterval A N ∧
    ∀ x ∈ ground N, x ∉ A → ¬IsSidonFinset (insert x A)

/-- Midpoint obstructions `x = (a + b) / 2` coming from equal-sum collisions
with the pair `(x, x)`. -/
def midpointCandidates (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image fun ab => (ab.1 + ab.2) / 2

/-- Sum-difference obstructions `x = a + b - c` coming from equal-sum collisions
of the form `x + c = a + b`. -/
def sumDiffCandidates (A : Finset ℕ) : Finset ℕ :=
  ((A.product A).product A).image fun abc => abc.1.1 + abc.1.2 - abc.2

/-- The combined elementary obstruction family attached to `A`. -/
def allCandidates (A : Finset ℕ) : Finset ℕ :=
  A ∪ midpointCandidates A ∪ sumDiffCandidates A

/-- A finite Sidon set together with the elementary obstruction-cover property
that underlies the easy `Ω(N^{1/3})` lower bound for maximal Sidon sets. -/
def ObstructionCoveredInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  SidonInInterval A N ∧
    ∀ ⦃x : ℕ⦄, x ∈ ground N → x ∉ A → x ∈ midpointCandidates A ∪ sumDiffCandidates A

/-- Cubic-form packaging of the Erdős-Sárközy-Sós problem: is there a uniform
constant `C` such that for every `N` one can find a maximal Sidon subset
`A ⊆ {1, ..., N}` with `|A|^3 ≤ C N`? -/
def SmallMaximalSidonConjecture : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∃ A : Finset ℕ,
    IsMaximalSidonInInterval A N ∧ A.card ^ 3 ≤ C * N

@[simp] theorem mem_ground {N x : ℕ} :
    x ∈ ground N ↔ 1 ≤ x ∧ x ≤ N := by
  simp [ground]

@[simp] theorem mem_allCandidates {A : Finset ℕ} {x : ℕ} :
    x ∈ allCandidates A ↔
      x ∈ A ∨ x ∈ midpointCandidates A ∨ x ∈ sumDiffCandidates A := by
  simp [allCandidates]

/-- A midpoint collision yields a midpoint candidate. -/
theorem mem_midpointCandidates_of_eq {A : Finset ℕ} {a b x : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (h : a + b = 2 * x) :
    x ∈ midpointCandidates A := by
  refine Finset.mem_image.mpr ?_
  refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
  simp [h]

/-- A sum-difference collision yields a sum-difference candidate. -/
theorem mem_sumDiffCandidates_of_eq {A : Finset ℕ} {a b c x : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (h : x + c = a + b) :
    x ∈ sumDiffCandidates A := by
  refine Finset.mem_image.mpr ?_
  have hx : a + b - c = x := by omega
  refine ⟨((a, b), c), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩, ?_⟩
  simp [hx]

end MaximalSidonSets
