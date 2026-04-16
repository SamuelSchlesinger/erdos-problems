import Erdos.SunflowerLemma.Statement

/-
# Elementary Facts About the Sunflower Lemma

This file proves the exact `n = 1` base case for Erdős problem `#20`.
If every set in the family is a singleton, then any `k` distinct members form
a `k`-sunflower with empty core. Conversely, a family of only `k - 1`
singletons cannot contain a `k`-sunflower for cardinality reasons. Hence

`f(1, k) = k`

for every `k ≥ 1`.
-/
namespace SunflowerLemma

theorem uniform_mono {n : ℕ} {𝒜 ℬ : Finset (Finset ℕ)}
    (hsub : ℬ ⊆ 𝒜) (h𝒜 : Uniform n 𝒜) :
    Uniform n ℬ := by
  intro s hs
  exact h𝒜 s (hsub hs)

theorem inter_eq_empty_of_card_eq_one_of_ne
    {s t : Finset ℕ} (hs : s.card = 1) (ht : t.card = 1) (hst : s ≠ t) :
    s ∩ t = ∅ := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp ht
  by_cases hab : a = b
  · subst hab
    exfalso
    exact hst rfl
  · simp [hab]

theorem not_containsSunflower_of_card_lt {k : ℕ} {𝒜 : Finset (Finset ℕ)}
    (hcard : 𝒜.card < k) :
    ¬ ContainsSunflower k 𝒜 := by
  rintro ⟨𝒮, hsub, hS, _⟩
  have hle : 𝒮.card ≤ 𝒜.card := Finset.card_le_card hsub
  omega

theorem uniform_one_containsSunflower {k : ℕ} {𝒜 : Finset (Finset ℕ)}
    (h𝒜 : Uniform 1 𝒜) (hk : k ≤ 𝒜.card) :
    ContainsSunflower k 𝒜 := by
  rcases Finset.powersetCard_nonempty.2 hk with ⟨𝒮, h𝒮⟩
  refine ⟨𝒮, (Finset.mem_powersetCard.mp h𝒮).1, (Finset.mem_powersetCard.mp h𝒮).2, ∅, ?_⟩
  intro s hs
  refine ⟨Finset.empty_subset s, ?_⟩
  intro t ht hst
  exact inter_eq_empty_of_card_eq_one_of_ne
    ((uniform_mono (Finset.mem_powersetCard.mp h𝒮).1 h𝒜) s hs)
    ((uniform_mono (Finset.mem_powersetCard.mp h𝒮).1 h𝒜) t ht)
    hst

/-- The family of all singleton subsets of `{0, …, r-1}`. -/
def singletonFamily (r : ℕ) : Finset (Finset ℕ) :=
  (Finset.range r).image fun i => ({i} : Finset ℕ)

theorem singletonFamily_uniform (r : ℕ) :
    Uniform 1 (singletonFamily r) := by
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨x, -, rfl⟩
  simp

theorem singletonFamily_card (r : ℕ) :
    (singletonFamily r).card = r := by
  classical
  unfold singletonFamily
  rw [Finset.card_image_of_injOn]
  · simp
  · intro x hx y hy hxy
    simpa using Finset.singleton_injective hxy

theorem sunflowerBound_one (k : ℕ) :
    SunflowerBound 1 k k := by
  intro 𝒜 h𝒜 hk
  exact uniform_one_containsSunflower h𝒜 hk

theorem le_of_mem_bounds_one {k m : ℕ} (hk : 1 ≤ k)
    (hm : m ∈ {m : ℕ | SunflowerBound 1 k m}) :
    k ≤ m := by
  by_contra hmk
  have hmle : m ≤ k - 1 := by omega
  let 𝒜 : Finset (Finset ℕ) := singletonFamily (k - 1)
  have huni : Uniform 1 𝒜 := singletonFamily_uniform (k - 1)
  have hcard_ge : m ≤ 𝒜.card := by
    simpa [𝒜, singletonFamily_card] using hmle
  have hsun : ContainsSunflower k 𝒜 := hm 𝒜 huni hcard_ge
  have hcard_eq : 𝒜.card = k - 1 := by
    simpa [𝒜] using singletonFamily_card (k - 1)
  have hsmall : 𝒜.card < k := by
    omega
  exact not_containsSunflower_of_card_lt hsmall hsun

theorem k_le_sunflowerNumber_one (k : ℕ) (hk : 1 ≤ k) :
    k ≤ sunflowerNumber 1 k := by
  have hne : ({m : ℕ | SunflowerBound 1 k m} : Set ℕ).Nonempty :=
    ⟨k, sunflowerBound_one k⟩
  exact le_of_mem_bounds_one hk (Nat.sInf_mem hne)

theorem sunflowerNumber_one_le (k : ℕ) :
    sunflowerNumber 1 k ≤ k := by
  exact Nat.sInf_le (show k ∈ {m : ℕ | SunflowerBound 1 k m} by exact sunflowerBound_one k)

/-- Exact one-uniform base case of the sunflower threshold. -/
theorem sunflowerNumber_one (k : ℕ) (hk : 1 ≤ k) :
    sunflowerNumber 1 k = k := by
  exact le_antisymm (sunflowerNumber_one_le k) (k_le_sunflowerNumber_one k hk)

end SunflowerLemma
