/-
# Supersaturation for Unit Fraction Triples

## The supersaturation paradigm

The packing-bound approach (VanDoorn.lean, StarNeighborhood.lean) uses disjoint
gadgets to force exclusions from triple-free sets. It is effective but limited:
the gadgets cover only a parametric subfamily of [1,N], and the 9/10 bound is
tight for the S+T family approach (see the third-family barrier in VanDoorn.lean).

Supersaturation takes a dual view. Instead of finding disjoint structures that
each force a fixed number of exclusions, it leverages the fact that **every**
element a ∈ A generates triples — and triple-freeness forces those triples'
endpoints outside A. The per-element exclusion footprint is proportional to
τ(a²), the number of divisors of a².

## Key facts (established in this file)

1. **Per-element exclusion** (`triple_free_forces_exclusion`): For a ∈ A
   (triple-free) and each divisor d of a² with 1 ≤ d < a, at least one of
   {a+d, a+a²/d} is not in A. This follows directly from the triple
   (a, a+d, a+a²/d) being forbidden.

2. **Endpoint separation** (`exclusion_endpoints_pairwise_disjoint`): The
   endpoint pairs from different divisors d₁ ≠ d₂ are disjoint (all four
   values are distinct). This makes the exclusion count tight: each a ∈ A
   forces exactly (τ(a²)−1)/2 independent "either-or" constraints on
   disjoint pairs of elements.

3. **Consecutive exclusion** (`triple_free_consecutive_exclusion`): Taking
   d = 1 gives the cleanest special case: a ∈ A with a ≥ 2 implies
   {a+1, a+a²} cannot both be in A.

4. **Endpoint multiplicity** (`endpoint_dvd_sq`, `endpoint_dvd_sq_iff`):
   d | a² ↔ d | (a+d)², characterizing which sources share a given endpoint.
   This is the foundation for bounding multiplicity in the full program.

5. **Consecutive forcing** (`triple_free_consecutive_forces_complement`):
   If a, a+1 ∈ A with a ≥ 2, then a + a² ∉ A. Combined with strict
   monotonicity of a ↦ a + a² (`sq_add_strict_mono`), this yields an
   injective exclusion map from consecutive pair sources to [1,N] \ A.

6. **Counting bound** (`triple_free_consecutive_pair_bound`):
   |{a ∈ [2,M] ∩ A : a+1 ∈ A}| + |A| ≤ N (where M² + M ≤ N).
   End-to-end proof combining exclusion, injectivity, and disjointness.

## Program for supersaturation bounds

**Step A** (complete): Per-element exclusion infrastructure.

**Step B** (partial): Double-counting for the d = 1 case. The map
a ↦ a + a² is shown to be strictly monotone (hence injective), and each
consecutive pair {a, a+1} ⊆ A forces a + a² ∈ [1,N] \ A. The full
double-counting over all divisors d | a² would require summing the
per-element exclusion counts:
  ∑_{a ∈ A, a ≤ √N} (τ(a²)−1)/2 ≤ |[1,N] \ A| · (max multiplicity)
This remains future work.

**Step C** (partial): Multiplicity infrastructure. The key identity
d | a² ↔ d | (a+d)² is formalized, characterizing when different sources
share an endpoint. The full multiplicity bound (an element x appears as
an endpoint for at most τ(x²) sources) and its average over [1,N]
requires the average order of τ(n²), which is analytic number theory.

**Step D** (partial): Extracting a bound. For d = 1, the consecutive pair
count gives |A| ≤ N − |P| where |P| ≤ M − 1 ≈ √N, yielding
|A| ≤ N − O(√N). This is weaker than VanDoorn's 9/10·N but serves as
a proof of concept for the supersaturation paradigm. The full bound
(using average τ(n²) ∼ c·log²n) would require Mathlib extensions for
Dirichlet series and mean-value estimates of multiplicative functions.
-/
import Erdos.UnitFractionTriples.Classification

namespace UnitFractionTriples

/-! ### Core exclusion -/

/-- **Per-element per-divisor exclusion.**

    If A is triple-free and a ∈ A, then for each divisor d of a² with d < a,
    the triple (a, a+d, a+a²/d) forces at least one endpoint outside A.

    This is the engine driving supersaturation: each element a ∈ A generates
    (τ(a²)−1)/2 independent exclusion constraints. -/
theorem triple_free_forces_exclusion (A : Finset ℕ) (hA : TripleFree A)
    {a : ℕ} (ha : a ∈ A) (ha_pos : 0 < a)
    {d : ℕ} (hd : 0 < d) (hdvd : d ∣ a ^ 2) (hda : d < a) :
    a + d ∉ A ∨ a + a ^ 2 / d ∉ A := by
  -- Get the triple identity and ordering from Classification.lean
  obtain ⟨htrip, _, _, _⟩ := triple_from_divisor ha_pos hd hdvd (le_of_lt hda)
  set b := a + d
  set c := a + a ^ 2 / d
  -- b < c since d < a implies d < a²/d (both factors of a² can't be < a)
  have h_cancel : d * (a ^ 2 / d) = a ^ 2 := Nat.mul_div_cancel' hdvd
  have hbc : b < c := by
    change a + d < a + a ^ 2 / d
    apply Nat.add_lt_add_left
    by_contra hle; push_neg at hle
    have : a ^ 2 ≤ d * d := by
      calc a ^ 2 = d * (a ^ 2 / d) := h_cancel.symm
        _ ≤ d * d := mul_le_mul_of_nonneg_left hle (Nat.zero_le d)
    nlinarith
  -- Convert to the rational equation 1/a = 1/b + 1/c
  have hb_pos : (0 : ℕ) < b := by omega
  have hc_pos : (0 : ℕ) < c := by omega
  have htrip_rat : (1 / a : ℚ) = 1 / b + 1 / c :=
    (triple_iff_div ha_pos hb_pos hc_pos).mpr htrip
  -- Suppose both endpoints are in A; derive contradiction with TripleFree
  by_contra h; push_neg at h; obtain ⟨hb_mem, hc_mem⟩ := h
  exact hA a ha b hb_mem c hc_mem (by omega) (by omega) (by omega)
    ⟨ha_pos, hb_pos, hc_pos, htrip_rat⟩

/-! ### Concrete exclusion instances -/

/-- **Consecutive exclusion (d = 1).**

    If a ∈ A (triple-free) with a ≥ 2, then {a+1, a²+a} ⊄ A.
    This is the identity 1/a = 1/(a+1) + 1/(a²+a).

    The simplest and most universal supersaturation constraint:
    every element a ≥ 2 in a triple-free set blocks either a+1 or a(a+1). -/
theorem triple_free_consecutive_exclusion (A : Finset ℕ) (hA : TripleFree A)
    {a : ℕ} (ha : a ∈ A) (ha2 : 2 ≤ a) :
    a + 1 ∉ A ∨ a + a ^ 2 ∉ A := by
  have h := triple_free_forces_exclusion A hA ha (by omega) (by omega : (0 : ℕ) < 1)
    (one_dvd _) (by omega : (1 : ℕ) < a)
  simpa [Nat.div_one] using h

/-! ### Endpoint separation

The "small" endpoints a+d (with d < a) lie in (a, 2a),
while the "large" endpoints a+a²/d lie in (2a, a+a²].
This separation ensures endpoint pairs from different divisors
are pairwise disjoint. -/

/-- For d < a dividing a², the small endpoint a+d is below 2a
    and the large endpoint a+a²/d is above 2a. -/
theorem exclusion_endpoint_ranges {a d : ℕ} (_ha : 0 < a)
    (hd : 0 < d) (hdvd : d ∣ a ^ 2) (hda : d < a) :
    a + d < 2 * a ∧ 2 * a < a + a ^ 2 / d := by
  have h_cancel : d * (a ^ 2 / d) = a ^ 2 := Nat.mul_div_cancel' hdvd
  constructor
  · omega
  · -- Need: a < a²/d. Since d < a, we get d² < a², so d < a²/d.
    suffices a < a ^ 2 / d by omega
    by_contra hle; push_neg at hle
    have h1 : a ^ 2 ≤ d * a := by
      calc a ^ 2 = d * (a ^ 2 / d) := h_cancel.symm
        _ ≤ d * a := mul_le_mul_of_nonneg_left hle (Nat.zero_le d)
    nlinarith

/-- **Endpoint pair disjointness.**

    For d₁ ≠ d₂ both dividing a² with d₁, d₂ < a, the sets
    {a+d₁, a+a²/d₁} and {a+d₂, a+a²/d₂} are disjoint.

    *Proof*: The small endpoints (< 2a) are distinguished by d₁ ≠ d₂.
    The large endpoints (> 2a) are distinguished by injectivity of
    d ↦ a²/d on divisors. Small and large endpoints can't collide
    because they're on opposite sides of 2a.

    This is the key structural fact making supersaturation counts tight:
    the (τ(a²)−1)/2 exclusion pairs are fully independent. -/
theorem exclusion_endpoints_pairwise_disjoint {a d₁ d₂ : ℕ} (ha : 0 < a)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hdvd₁ : d₁ ∣ a ^ 2) (hdvd₂ : d₂ ∣ a ^ 2)
    (hda₁ : d₁ < a) (hda₂ : d₂ < a) (hne : d₁ ≠ d₂) :
    a + d₁ ≠ a + d₂ ∧
    a + d₁ ≠ a + a ^ 2 / d₂ ∧
    a + a ^ 2 / d₁ ≠ a + d₂ ∧
    a + a ^ 2 / d₁ ≠ a + a ^ 2 / d₂ := by
  obtain ⟨h1s, h1l⟩ := exclusion_endpoint_ranges ha hd₁ hdvd₁ hda₁
  obtain ⟨h2s, h2l⟩ := exclusion_endpoint_ranges ha hd₂ hdvd₂ hda₂
  -- Small ≠ small: immediate from d₁ ≠ d₂
  -- Small ≠ large: opposite sides of 2a
  -- Large ≠ large: cancellation law
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro heq
  have h_div_eq : a ^ 2 / d₁ = a ^ 2 / d₂ := by omega
  have hc₁ : d₁ * (a ^ 2 / d₁) = a ^ 2 := Nat.mul_div_cancel' hdvd₁
  have hc₂ : d₂ * (a ^ 2 / d₂) = a ^ 2 := Nat.mul_div_cancel' hdvd₂
  rw [h_div_eq] at hc₁
  -- Now hc₁ : d₁ * (a²/d₂) = a², hc₂ : d₂ * (a²/d₂) = a²
  -- So d₁ * q = d₂ * q where q = a²/d₂ > 0, giving d₁ = d₂
  have hq_pos : 0 < a ^ 2 / d₂ :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hdvd₂) hd₂
  exact hne (mul_right_cancel₀ (by omega : (a ^ 2 / d₂ : ℕ) ≠ 0) (hc₁.trans hc₂.symm))

/-! ### Multiplicity infrastructure (Step C)

An element x appears as a "small" exclusion endpoint a + d (with d | a², d < a)
for some source a. This section characterizes which (a, d) pairs produce a given
endpoint x, via the identity d | a² ↔ d | (a+d)². -/

/-- d | a² implies d | (a+d)². The algebraic identity (a+d)² = a² + d(2a+d)
    makes divisibility transparent.

    This is the foundation for multiplicity analysis: if x = a + d is an
    endpoint, then d = x − a divides a², hence divides x². So the multiplicity
    of x as an endpoint is bounded by |{d : d | x², 0 < d < x}|. -/
theorem endpoint_dvd_sq {a d : ℕ} (hdvd : d ∣ a ^ 2) :
    d ∣ (a + d) ^ 2 := by
  have key : (a + d) ^ 2 = a ^ 2 + d * (2 * a + d) := by ring
  rw [key]
  exact dvd_add hdvd (dvd_mul_right d _)

/-- d | a² ↔ d | (a+d)². The reverse direction uses the identity
    (a+d)² = a² + d(2a+d) and `Nat.dvd_add_left`. -/
theorem endpoint_dvd_sq_iff {a d : ℕ} :
    d ∣ a ^ 2 ↔ d ∣ (a + d) ^ 2 := by
  constructor
  · exact endpoint_dvd_sq
  · intro h
    have key : (a + d) ^ 2 = a ^ 2 + d * (2 * a + d) := by ring
    rw [key] at h
    exact (Nat.dvd_add_left (dvd_mul_right d _)).mp h

/-! ### Counting infrastructure (Step B)

The exclusion map a ↦ a + a² = a(a+1) sends each "consecutive pair source"
(an element a ∈ A with a+1 ∈ A) to a forced non-member of A. Strict
monotonicity of this map ensures the excluded elements are distinct, enabling
a counting argument. -/

/-- a + a² is strictly monotone: a₁ < a₂ → a₁ + a₁² < a₂ + a₂².
    This ensures the exclusion map a ↦ a + a² is injective, making
    the excluded elements from different sources distinct. -/
theorem sq_add_strict_mono {a₁ a₂ : ℕ} (h : a₁ < a₂) :
    a₁ + a₁ ^ 2 < a₂ + a₂ ^ 2 := by
  zify at h ⊢; nlinarith [sq_nonneg ((a₂ : ℤ) - a₁)]

/-- If a, a+1 ∈ A (triple-free) with a ≥ 2, then a + a² ∉ A.
    Resolves the disjunction from `triple_free_consecutive_exclusion`
    when a+1 is known to be in A. -/
theorem triple_free_consecutive_forces_complement (A : Finset ℕ) (hA : TripleFree A)
    {a : ℕ} (ha : a ∈ A) (ha1 : a + 1 ∈ A) (ha2 : 2 ≤ a) :
    a + a ^ 2 ∉ A := by
  rcases triple_free_consecutive_exclusion A hA ha ha2 with h | h
  · exact absurd ha1 h
  · exact h

/-! ### End-to-end counting bound (Steps B + D)

We combine the per-element exclusion (Step A), injectivity (Step B), and
a straightforward counting argument (Step D) to obtain the first complete
supersaturation bound. The d = 1 special case yields:

  |{a ∈ [2,M] ∩ A : a+1 ∈ A}| + |A| ≤ N

*Limitation*: This is weaker than VanDoorn's 9/10 bound, recovering only
|A| ≤ N − O(√N). The full supersaturation program (using all divisors d | a²
and the average order of τ(n²) ∼ c·log²n from analytic number theory) would
yield stronger bounds but requires Mathlib extensions for Dirichlet series
and mean-value estimates of multiplicative functions. The infrastructure in
this file (endpoint divisibility, monotonicity, disjoint exclusion) lays the
foundation for such future work. -/

/-- **Consecutive pair counting bound.**

    If A ⊆ [1,N] is triple-free, the number of "consecutive pairs"
    {a, a+1} ⊆ A with a ∈ [2,M] (where M²+M ≤ N) plus |A| is at most N.
    Each consecutive pair forces a distinct element a+a² ∈ [1,N] \ A via the
    identity 1/a = 1/(a+1) + 1/(a²+a). The map a ↦ a+a² is injective
    (by `sq_add_strict_mono`), so these excluded elements are distinct. -/
theorem triple_free_consecutive_pair_bound (N M : ℕ) (A : Finset ℕ)
    (hA : TripleFree A) (hAN : A ⊆ Finset.Icc 1 N)
    (hM : M ^ 2 + M ≤ N) :
    ((Finset.Icc 2 M).filter (fun a => a ∈ A ∧ a + 1 ∈ A)).card + A.card ≤ N := by
  set P := (Finset.Icc 2 M).filter (fun a => a ∈ A ∧ a + 1 ∈ A)
  -- The exclusion map a ↦ a + a² and its image
  have hf_mono : StrictMono (fun (a : ℕ) => a + a ^ 2) :=
    fun _ _ h => sq_add_strict_mono h
  set E := P.image (fun a => a + a ^ 2)
  -- E ⊆ [1,N]: each a ∈ [2,M] maps to a+a² ∈ [6, M²+M] ⊆ [1,N]
  have hE_sub : E ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨haIcc, ha_A, ha1_A⟩ := Finset.mem_filter.mp haP
    rw [Finset.mem_Icc] at haIcc ⊢
    obtain ⟨ha_ge, ha_le⟩ := haIcc
    refine ⟨by linarith [Nat.zero_le (a ^ 2)], ?_⟩
    -- a + a² = a(a+1) ≤ M(M+1) = M² + M ≤ N
    have h_sq : a * a ≤ M * M := Nat.mul_le_mul ha_le ha_le
    nlinarith [show a ^ 2 = a * a from by ring, show M ^ 2 = M * M from by ring]
  -- E ∩ A = ∅: each a+a² is excluded from A by consecutive forcing
  have hE_disj : Disjoint E A := by
    rw [Finset.disjoint_left]
    intro x hxE hxA
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hxE
    obtain ⟨haIcc, ha_A, ha1_A⟩ := Finset.mem_filter.mp haP
    rw [Finset.mem_Icc] at haIcc
    exact absurd hxA (triple_free_consecutive_forces_complement A hA ha_A ha1_A haIcc.1)
  -- |E| = |P| by injectivity of a ↦ a + a²
  have hcard_eq : E.card = P.card :=
    Finset.card_image_of_injective P hf_mono.injective
  -- Combine: |P| + |A| = |E| + |A| = |E ∪ A| ≤ |[1,N]| = N
  calc P.card + A.card
      = E.card + A.card := by rw [hcard_eq]
    _ = (E ∪ A).card := (Finset.card_union_of_disjoint hE_disj).symm
    _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card (Finset.union_subset hE_sub hAN)
    _ = N := by simp

end UnitFractionTriples
