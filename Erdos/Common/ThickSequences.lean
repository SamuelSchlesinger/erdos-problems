/-
# Thick Sequences and Multiples — Shared Infrastructure

Reusable vocabulary for "thick" sequences (those whose reciprocals diverge),
their sets of multiples, and Behrend-type density statements.

A sequence of naturals `(aᵢ)` is *thick* when `Σ 1/aᵢ = ∞`. The set of its
multiples is `{n · aᵢ : n ∈ ℕ, i ∈ ι}`. The sequence is *Behrend* when this
set has natural density `1`, and *weakly Behrend with respect to ε* when the
lower density of its multiples is at least `1 - ε`.

These notions appear across several Erdős problems:
- `#9`–`#11`: covering systems and Behrend-style problems on multiples,
- `#25` (residue-class avoidance): the avoided set is the complement of a
  countable union of residue classes, i.e. the complement of a union of
  arithmetic progressions, each of which is a translate of multiples,
- `#26` (Tenenbaum-style thick sequences): direct subject.

Reference (vocabulary mined from): the proof structure of
`erdos_26.variants.tenenbaum.lean` in the public release
`google-deepmind/alphaproof-nexus-results` (Apache 2.0). The definitions
`IsThick` and `MultiplesOf` mirror Google DeepMind's `Erdos26.IsThick` and
`Erdos26.MultiplesOf`, with the same mathematical content but adapted to
live in our shared `Erdos.Common` namespace so that subsequent files in
`ResidueAvoidingDensity`, `UnitFractionPairs`, and related projects can
reuse them. The natural-density notion used by the DeepMind file
(`Set.HasDensity`, `Set.lowerDensity`) lives in their `ProblemImports`
prelude and is not in current Mathlib; we therefore define the natural
density of a set of naturals directly here as `Set.natDensityRatio` and
package the Behrend-type predicates around that.
-/
import Mathlib

set_option linter.style.header false

namespace Erdos.Common

/-! ### Thick sequences -/

/-- A sequence `A : ι → ℕ` is *thick* when its reciprocal series diverges:
`Σᵢ 1 / Aᵢ = ∞` (i.e. the reciprocal sequence is not summable in `ℝ`).

This is the natural divergence condition appearing in the statements of
Erdős problems `#9`, `#25`, `#26`, and many others: a "large" sequence in
the Erdős sense. -/
def IsThick {ι : Type*} (A : ι → ℕ) : Prop :=
  ¬ Summable (fun i ↦ (1 : ℝ) / A i)

/-- The set of multiples of a sequence `A : ι → ℕ` is
`{n · Aᵢ : n ∈ ℕ, i ∈ ι} = ⋃ᵢ {n · Aᵢ}_n`. -/
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ :=
  Set.range fun (p : ℕ × ι) => p.1 * A p.2

/-- The set of multiples of a *shifted* sequence `Aᵢ + k`. This is the
correct object for residue-class avoidance: the multiples of `Aᵢ + k`
are exactly the integers congruent to `0 mod (Aᵢ + k)`, hence "swept out"
by the residue class. -/
def ShiftedMultiplesOf {ι : Type*} (A : ι → ℕ) (k : ℕ) : Set ℕ :=
  MultiplesOf (fun i => A i + k)

/-! ### Natural density for sets of positive integers

We bundle the "finite count up to `N`" view of natural density that is
needed when reasoning about `MultiplesOf` and avoided sets. -/

/-- The number of integers in `{1, 2, …, N}` that lie in `A`, as a real.
We supply classical decidability so that the membership predicate is
decidable for any abstract set. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact (((Finset.Icc 1 N).filter (· ∈ A) : Finset ℕ).card : ℝ)

/-- The natural-density ratio `|A ∩ [1, N]| / N`, with the convention that
the ratio at `N = 0` is `0`. -/
noncomputable def natDensityRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else countUpTo A N / N

/-- A set has *natural density* `d` if `|A ∩ [1, N]| / N → d`. -/
def HasNatDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => natDensityRatio A N) Filter.atTop (nhds d)

/-! ### Behrend-style density conditions -/

/-- A sequence `A : ι → ℕ` is *Behrend* when almost every natural number is a
multiple of some `Aᵢ`, i.e. when `MultiplesOf A` has natural density `1`. -/
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop :=
  HasNatDensity (MultiplesOf A) 1

/-- A sequence `A : ι → ℕ` is *weakly Behrend with respect to* `ε ∈ ℝ`
when at least `1 - ε` density of integers `≤ N` are multiples of some `Aᵢ`,
in the limit. We use the `liminf` of the count ratios as the lower density. -/
def IsWeaklyBehrend {ι : Type*} (A : ι → ℕ) (ε : ℝ) : Prop :=
  (1 - ε : ℝ) ≤ Filter.liminf (fun N : ℕ => natDensityRatio (MultiplesOf A) N)
    Filter.atTop

/-! ### Elementary structural lemmas -/

/-- The set of multiples of `A` is the indexed union of the sets of
multiples of each `A i`. -/
theorem multiplesOf_eq_iUnion {ι : Type*} (A : ι → ℕ) :
    MultiplesOf A = ⋃ i, Set.range fun n : ℕ => n * A i := by
  ext m
  simp only [MultiplesOf, Set.mem_range, Set.mem_iUnion, Prod.exists]
  tauto

/-- The shifted multiples set is the indexed union of multiples of each
`A i + k`. -/
theorem shiftedMultiplesOf_eq_iUnion {ι : Type*} (A : ι → ℕ) (k : ℕ) :
    ShiftedMultiplesOf A k = ⋃ i, Set.range fun n : ℕ => n * (A i + k) := by
  simp [ShiftedMultiplesOf, multiplesOf_eq_iUnion]

/-- Zero is always a multiple of every element of every sequence: take `n = 0`.
This lets one always assume `0 ∈ MultiplesOf A` when the index type is
inhabited. -/
theorem zero_mem_multiplesOf {ι : Type*} [Nonempty ι] (A : ι → ℕ) :
    (0 : ℕ) ∈ MultiplesOf A :=
  ⟨(0, Classical.arbitrary _), by simp⟩

/-- Every element `A i` itself is a multiple of `A i`: take `n = 1`. -/
theorem self_mem_multiplesOf {ι : Type*} (A : ι → ℕ) (i : ι) :
    A i ∈ MultiplesOf A := by
  refine ⟨(1, i), ?_⟩
  simp

/-- Containment between two sequences gives containment between their
multiples sets, in the sense that if every value `B j` is some `A i`
(as natural numbers) then `MultiplesOf B ⊆ MultiplesOf A`. -/
theorem multiplesOf_subset_of_range_subset
    {ι ι' : Type*} (A : ι → ℕ) (B : ι' → ℕ)
    (h : ∀ j, ∃ i, A i = B j) :
    MultiplesOf B ⊆ MultiplesOf A := by
  rintro m ⟨⟨n, j⟩, rfl⟩
  obtain ⟨i, hi⟩ := h j
  exact ⟨(n, i), by simp [hi]⟩

/-- A reindexing of a sequence has the same multiples set. -/
theorem multiplesOf_reindex {ι ι' : Type*} (A : ι → ℕ) (e : ι' → ι)
    (he : Function.Surjective e) :
    MultiplesOf (A ∘ e) = MultiplesOf A := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro m ⟨⟨n, j⟩, rfl⟩
    exact ⟨(n, e j), rfl⟩
  · rintro m ⟨⟨n, i⟩, rfl⟩
    obtain ⟨j, rfl⟩ := he i
    exact ⟨(n, j), rfl⟩

/-! ### Thickness lemmas -/

/-- A finite sequence of positive naturals is never thick: a finite sum of
positive reals is summable. -/
theorem not_isThick_of_finite {ι : Type*} [Finite ι] (A : ι → ℕ) :
    ¬ IsThick A := by
  intro h
  exact h Summable.of_finite

/-! ### Sanity checks -/

/-- Any finite indexed sequence is non-thick (degenerate case). -/
example : ¬ IsThick (fun _ : Fin 5 => 7) := not_isThick_of_finite _

/-- The identity sequence `n ↦ n` on `ℕ` is thick: its reciprocals are the
divergent harmonic series. -/
example : IsThick (fun n : ℕ => n) := Real.not_summable_one_div_natCast

end Erdos.Common
