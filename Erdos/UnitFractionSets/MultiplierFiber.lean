/-
# Multiplier-Fiber Reduction for Problem #301

If a ∈ A and all RHS elements are multiples of a, say bᵢ = a·kᵢ, then
1/a = Σ 1/(a·kᵢ) ⟺ 1 = Σ 1/kᵢ. This reformulates the global SumFree
condition as per-element "Egyptian-1-avoiding" constraints on multiplier fibers.

Define the **multiplier fiber** of a in A:
  K_a = { b/a : b ∈ A \ {a}, a ∣ b }
Then SumFree(A) implies: for every a ∈ A, no nonempty subset of K_a has
reciprocal sum equal to 1.

This is the "easy" (statement) part of the multiplier-fiber program.
The "hard" part — exploiting density forcing on fibers — remains research-level.

Reference: https://www.erdosproblems.com/301
-/
import Erdos.UnitFractionSets.Statement
import Erdos.WeirdNumbers.DivisorEgyptianFree

namespace UnitFractionSets

open Finset

/-- A finite set of positive integers is **EgyptianOneFree** if no nonempty
    subset has reciprocals summing to exactly 1.

    This is the per-fiber constraint that SumFree imposes: if a ∈ A and
    K_a is the multiplier fiber, then K_a must be EgyptianOneFree. -/
def EgyptianOneFree (K : Finset ℕ) : Prop :=
  ¬∃ T ⊆ K, T.Nonempty ∧ ∑ k ∈ T, (1 / (k : ℚ)) = 1

/-- The **multiplier fiber** of `a` in `A`: the set of multipliers `b/a`
    for elements `b ∈ A \ {a}` that are divisible by `a`.

    Concretely: `MultiplierFiber A a = { b / a : b ∈ A \ {a}, a ∣ b }`. -/
def MultiplierFiber (A : Finset ℕ) (a : ℕ) : Finset ℕ :=
  ((A.erase a).filter (a ∣ ·)).image (· / a)

/-! ## Fiber membership API -/

/-- If `k` is in the multiplier fiber of `a`, then `a * k ∈ A` and `a * k ≠ a`. -/
theorem mul_div_mem_of_mem_fiber {A : Finset ℕ} {a k : ℕ} (ha : 0 < a)
    (hk : k ∈ MultiplierFiber A a) : a * k ∈ A ∧ a * k ≠ a := by
  simp only [MultiplierFiber, mem_image, mem_filter, mem_erase] at hk
  obtain ⟨b, ⟨⟨hba, hbA⟩, hab⟩, hk_eq⟩ := hk
  obtain ⟨d, hd⟩ := hab
  subst hd
  rw [Nat.mul_div_cancel_left _ ha] at hk_eq
  subst hk_eq
  exact ⟨hbA, hba⟩

/-- If `a * k ∈ A` with `k ≥ 2` and `a > 0`, then `k ∈ MultiplierFiber A a`. -/
theorem mem_fiber_of_mul_mem {A : Finset ℕ} {a k : ℕ} (ha : 0 < a) (hk : 2 ≤ k)
    (hm : a * k ∈ A) : k ∈ MultiplierFiber A a := by
  simp only [MultiplierFiber, mem_image, mem_filter, mem_erase]
  refine ⟨a * k, ⟨⟨?_, hm⟩, dvd_mul_right a k⟩, Nat.mul_div_cancel_left k ha⟩
  intro h
  have : a * 2 ≤ a * k := Nat.mul_le_mul_left a hk
  omega

/-! ## Core theorem: SumFree implies fibers are EgyptianOneFree -/

/-- **Multiplier-fiber reduction.**

    If A is SumFree and a ∈ A with a > 0, then the multiplier fiber K_a
    is EgyptianOneFree: no nonempty T ⊆ K_a has Σ 1/k = 1.

    **Proof idea:** Suppose T ⊆ K_a with Σ_{k ∈ T} 1/k = 1. Build
    S = { a * k : k ∈ T } ⊆ A \ {a}. Then
      Σ_{b ∈ S} 1/b = Σ_{k ∈ T} 1/(a·k) = (1/a) · Σ 1/k = 1/a,
    contradicting SumFree(A). -/
theorem sum_free_fiber_egyptian_free {A : Finset ℕ} {a : ℕ}
    (hA : SumFree A) (haA : a ∈ A) (ha : 0 < a) :
    EgyptianOneFree (MultiplierFiber A a) := by
  intro ⟨T, hTsub, hTne, hTsum⟩
  -- Build S = T.image (a * ·) ⊆ A.erase a
  let S := T.image (a * ·)
  -- The map k ↦ a * k is injective (a > 0)
  have ha0 : a ≠ 0 := by omega
  have hinj : Set.InjOn (a * ·) ↑T :=
    fun _ _ _ _ h => mul_left_cancel₀ ha0 h
  -- S ⊆ A.erase a: each a*k corresponds to some b ∈ A \ {a} via fiber membership
  have hSsub : S ⊆ A.erase a := by
    intro b hb
    simp only [S, mem_image] at hb
    obtain ⟨k, hkT, rfl⟩ := hb
    have ⟨hm, hne⟩ := mul_div_mem_of_mem_fiber ha (hTsub hkT)
    exact mem_erase.mpr ⟨hne, hm⟩
  -- S is nonempty
  have hSne : S.Nonempty := hTne.image _
  -- Σ_{b ∈ S} 1/b = (1/a) · Σ_{k ∈ T} 1/k = 1/a
  have hSsum : (1 / a : ℚ) = ∑ b ∈ S, (1 / (b : ℚ)) := by
    rw [Finset.sum_image hinj]
    have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
    have hcongr : ∀ k ∈ T, (1 : ℚ) / (↑(a * k)) = 1 / a * (1 / k) := by
      intro k _
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, hTsum, mul_one]
  -- Contradiction with SumFree
  exact hA a haA S hSsub hSne hSsum

/-! ## Bridge to #470 (DivisorEgyptianFree) -/

/-- **DivisorEgyptianFree ↔ EgyptianOneFree on divisors.**

    The weird-number predicate `DivisorEgyptianFree(n)` (no nonempty
    T ⊆ divisors(n) \ {1} with Σ 1/t = 1) is exactly `EgyptianOneFree`
    applied to `n.divisors.erase 1`.

    This connects the #470 framework to the #301 fiber framework:
    both are instances of the same "no subset sums to 1" property. -/
theorem divisor_egyptian_free_iff_egyptian_one_free {n : ℕ} (_hn : 0 < n) :
    WeirdNumbers.DivisorEgyptianFree n ↔ EgyptianOneFree (n.divisors.erase 1) := by
  constructor
  · -- Forward: DivisorEgyptianFree → EgyptianOneFree(divisors \ {1})
    intro hdef ⟨T, hTsub, hTne, hTsum⟩
    apply hdef
    refine ⟨T, hTsub.trans (erase_subset 1 n.divisors), ?_, hTne, hTsum⟩
    intro h1
    have := hTsub h1
    simp [mem_erase] at this
  · -- Backward: EgyptianOneFree(divisors \ {1}) → DivisorEgyptianFree
    intro heof ⟨T, hTdiv, h1, hTne, hTsum⟩
    apply heof
    refine ⟨T, fun x hx => mem_erase.mpr ⟨fun h1x => h1 (h1x ▸ hx), hTdiv hx⟩,
            hTne, hTsum⟩

end UnitFractionSets
