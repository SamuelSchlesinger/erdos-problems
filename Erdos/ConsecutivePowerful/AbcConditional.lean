/-
# Conditional Finiteness of Consecutive Powerful Triples

The Erdős problem #364 asks whether there are any triples `(n, n+1, n+2)` of
consecutive powerful numbers. Even an *infinitude* result would be a major
advance; the rigid expectation is finiteness, perhaps even non-existence.

This file records the standard conditional result: **assuming the abc
conjecture, only finitely many such triples can exist.** The proof goes via:

1. The radical bound `rad(n)² ∣ n`, hence `rad(n) ≤ √n`, for powerful `n`
   (`radical_sq_dvd_of_powerful`, `radical_le_sqrt_of_powerful`).
2. Applied to the identity `1 + n(n+2) = (n+1)²`, the abc conjecture forces
   `n` bounded: the radical of the product is at most `√(n(n+1)(n+2))`, and
   `(n+1)²` grows like `n²`, so any sub-quadratic upper bound — which abc
   delivers for `ε < 1/3` — suffices.

## Main results

* `radical_sq_dvd_of_powerful`: for powerful `n > 0` we have `rad(n)² ∣ n`.
* `radical_le_sqrt_of_powerful`: the real-valued reformulation
  `rad(n) ≤ √n`.
* `AbcConjecture`: the statement of the abc conjecture in terms of natural
  numbers.
* `finitely_many_consecutive_powerful_of_abc`: conditional on
  `AbcConjecture`, the set of starts of consecutive powerful triples is
  finite.
-/
import Erdos.ConsecutivePowerful.Search
import Mathlib.RingTheory.Radical

namespace ConsecutivePowerful

open UniqueFactorizationMonoid

/-! ### Radical bound `rad(n)² ∣ n` for powerful `n`. -/

/-- `Nat`-flavoured form of `UniqueFactorizationMonoid.radical` as a product
over `Nat.primeFactors`. -/
private lemma radical_eq_prod_primeFactors (n : ℕ) :
    (radical n : ℕ) = ∏ p ∈ n.primeFactors, p := by
  unfold UniqueFactorizationMonoid.radical
  rw [UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
  rfl

/-- For powerful `n > 0`, the square of the radical divides `n`: every prime
factor appears in `n` with exponent at least `2`, so `(∏ p)² = ∏ p² ∣ ∏ p^{e_p} = n`. -/
theorem radical_sq_dvd_of_powerful {n : ℕ} (hn : Powerful n) :
    (radical n : ℕ) ^ 2 ∣ n := by
  classical
  have hn0 : n ≠ 0 := hn.1.ne'
  have hn_eq : (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n := by
    have hprod : n.factorization.prod (· ^ ·) = n :=
      Nat.factorization_prod_pow_eq_self hn0
    rwa [Finsupp.prod, Nat.support_factorization] at hprod
  have hpow_dvd : ∀ p ∈ n.primeFactors, p ^ 2 ∣ p ^ (n.factorization p) := by
    intro p hp
    have hpow : 2 ≤ n.factorization p :=
      (powerful_iff_factorization_ge_two.mp hn).2 p hp
    exact pow_dvd_pow p hpow
  have hprod_dvd :
      (∏ p ∈ n.primeFactors, p ^ 2) ∣ (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) :=
    Finset.prod_dvd_prod_of_dvd _ _ hpow_dvd
  rw [radical_eq_prod_primeFactors, ← Finset.prod_pow]
  conv_rhs => rw [← hn_eq]
  exact hprod_dvd

/-- Real-valued form of the radical bound: for powerful `n > 0`, the radical
is at most `√n`. -/
theorem radical_le_sqrt_of_powerful {n : ℕ} (hn : Powerful n) :
    (((radical n : ℕ) : ℕ) : ℝ) ≤ Real.sqrt n := by
  have hsqd := radical_sq_dvd_of_powerful hn
  have hsqle : (radical n : ℕ) ^ 2 ≤ n := Nat.le_of_dvd hn.1 hsqd
  have hsqle_real : (((radical n : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsqle
  have hnonneg : 0 ≤ ((radical n : ℕ) : ℝ) := by positivity
  have hsqrt := Real.sqrt_le_sqrt hsqle_real
  rwa [Real.sqrt_sq hnonneg] at hsqrt

/-! ### Conditional finiteness via the abc conjecture. -/

/-- **The abc conjecture (statement only).**

For every `ε > 0` there exists a constant `K` such that whenever
`a + b = c` for *positive coprime* integers, we have
`c ≤ K · rad(abc)^(1+ε)`. -/
def AbcConjecture : Prop :=
  ∀ ε > (0 : ℝ), ∃ K : ℝ, ∀ a b c : ℕ,
    0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * ((radical ((a : ℕ) * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- The radical of `m^2` equals the radical of `m`. -/
private lemma radical_sq_nat (m : ℕ) : (radical (m^2) : ℕ) = (radical m : ℕ) := by
  by_cases hm : m = 0
  · subst hm
    simp
  exact_mod_cast (UniqueFactorizationMonoid.radical_pow m (n := 2) (by norm_num))

/-- Radical of a triple product is divided by the product of radicals.
We state this in the form we need for the abc bound. -/
private lemma radical_triple_dvd (x y z : ℕ) :
    (radical (x * y * z) : ℕ)
      ∣ (radical x : ℕ) * (radical y : ℕ) * (radical z : ℕ) := by
  refine (UniqueFactorizationMonoid.radical_mul_dvd (a := x * y) (b := z)).trans ?_
  exact mul_dvd_mul_right (UniqueFactorizationMonoid.radical_mul_dvd) _

/-- **Conditional finiteness of consecutive powerful triples.**

If the abc conjecture holds, then there are only finitely many starts of
consecutive powerful triples.

**Proof strategy.** From the identity `1 + n(n+2) = (n+1)²`, apply the abc
conjecture (with `ε = 1/4`) to `a = 1`, `b = n(n+2)`, `c = (n+1)²`.
Coprimality of `n(n+2)` and `(n+1)²` is automatic since `gcd(n, n+1) = 1` and
`gcd(n+2, n+1) = 1`.

The radical of the product `1 · n(n+2) · (n+1)²` divides
`rad(n)·rad(n+2)·rad((n+1)²) = rad(n)·rad(n+2)·rad(n+1)`. Using the powerful
bound `rad(m) ≤ √m`, we get

  `rad(n(n+2)(n+1)²) ≤ √n·√(n+1)·√(n+2) ≤ (n+2)^{3/2}`.

The abc inequality then gives `(n+1)² ≤ K · (n+2)^{(3/2)(5/4)} = K·(n+2)^{15/8}`.
Combined with `(n+1)² ≥ (n+2)²/4`, this yields `(n+2)^{1/8} ≤ 4K`, hence
`n + 2 ≤ (4K)^8`. The set in question is therefore contained in `Set.Iic N`
for a sufficiently large `N`, hence finite. -/
theorem finitely_many_consecutive_powerful_of_abc :
    AbcConjecture →
      Set.Finite { n : ℕ | Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) } := by
  intro habc
  obtain ⟨K, hK⟩ := habc (1/4) (by norm_num)
  -- Define an explicit numerical bound `N`.
  set N : ℕ := (⌈(4 * |K| + 1) ^ (8 : ℕ)⌉.toNat) + 10 with hN_def
  refine Set.Finite.subset (Set.finite_Iic N) ?_
  intro n hn
  obtain ⟨hpn, hpn1, hpn2⟩ := hn
  -- Trivial case: n = 0 is in Set.Iic N trivially.
  by_contra hlt
  simp only [Set.mem_Iic, not_le] at hlt
  -- We have n > N ≥ 10, in particular n ≥ 11.
  have hn_ge_1 : 1 ≤ n := by omega
  have hn_pos : 0 < n := hpn.1
  have hn1_pos : 0 < n + 1 := by omega
  have hn2_pos : 0 < n + 2 := by omega
  -- Step 1: Apply abc to (1, n(n+2), (n+1)²).
  have hsum : (1 : ℕ) + n * (n + 2) = (n + 1) ^ 2 := by ring
  have hcop : Nat.Coprime 1 (n * (n + 2)) := Nat.coprime_one_left _
  have hb_pos : 0 < n * (n + 2) := Nat.mul_pos hn_pos hn2_pos
  have habc_app :
      (((n + 1 : ℕ) ^ 2 : ℕ) : ℝ)
      ≤ K * ((radical (1 * (n * (n + 2)) * (n + 1) ^ 2) : ℕ) : ℝ) ^ (1 + (1/4 : ℝ)) :=
    hK 1 (n * (n + 2)) ((n + 1) ^ 2) (by norm_num) hb_pos hsum hcop
  -- Simplify `1 * x * y = x * y`.
  have hrewrite : (1 : ℕ) * (n * (n + 2)) * (n + 1) ^ 2
      = n * (n + 2) * (n + 1) ^ 2 := by ring
  rw [hrewrite] at habc_app
  -- Step 2: Bound the radical.
  have hrad_dvd :
      (radical (n * (n + 2) * (n + 1) ^ 2) : ℕ)
        ∣ (radical n : ℕ) * (radical (n + 2) : ℕ) * (radical (n + 1) : ℕ) := by
    have h1 : (radical (n * (n + 2) * (n + 1) ^ 2) : ℕ)
        ∣ (radical (n * (n + 2)) : ℕ) * (radical ((n + 1) ^ 2) : ℕ) :=
      UniqueFactorizationMonoid.radical_mul_dvd
    have h2 : (radical (n * (n + 2)) : ℕ)
        ∣ (radical n : ℕ) * (radical (n + 2) : ℕ) :=
      UniqueFactorizationMonoid.radical_mul_dvd
    have h3 : (radical ((n + 1) ^ 2) : ℕ) = (radical (n + 1) : ℕ) :=
      radical_sq_nat (n + 1)
    rw [h3] at h1
    exact h1.trans (mul_dvd_mul_right h2 _)
  have hradn_pos : 0 < (radical n : ℕ) := Nat.radical_pos n
  have hradn1_pos : 0 < (radical (n + 1) : ℕ) := Nat.radical_pos (n + 1)
  have hradn2_pos : 0 < (radical (n + 2) : ℕ) := Nat.radical_pos (n + 2)
  have hpos_rhs : 0 < (radical n : ℕ) * (radical (n + 2) : ℕ) * (radical (n + 1) : ℕ) := by
    positivity
  have hrad_le_nat :
      (radical (n * (n + 2) * (n + 1) ^ 2) : ℕ)
        ≤ (radical n : ℕ) * (radical (n + 2) : ℕ) * (radical (n + 1) : ℕ) :=
    Nat.le_of_dvd hpos_rhs hrad_dvd
  have hrad_le_real :
      ((radical (n * (n + 2) * (n + 1) ^ 2) : ℕ) : ℝ)
        ≤ ((radical n : ℕ) : ℝ) * ((radical (n + 2) : ℕ) : ℝ)
            * ((radical (n + 1) : ℕ) : ℝ) := by exact_mod_cast hrad_le_nat
  -- Step 3: Use the powerful bounds.
  have hrn := radical_le_sqrt_of_powerful hpn
  have hrn1 : ((radical (n + 1) : ℕ) : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    have := radical_le_sqrt_of_powerful hpn1
    convert this using 2
  have hrn2 : ((radical (n + 2) : ℕ) : ℝ) ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    have := radical_le_sqrt_of_powerful hpn2
    convert this using 2
  -- Combine the three bounds.
  have hr_nonneg : 0 ≤ ((radical n : ℕ) : ℝ) := by positivity
  have hr1_nonneg : 0 ≤ ((radical (n + 1) : ℕ) : ℝ) := by positivity
  have hr2_nonneg : 0 ≤ ((radical (n + 2) : ℕ) : ℝ) := by positivity
  have hs_nonneg : 0 ≤ Real.sqrt ((n : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hs1_nonneg : 0 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hs2_nonneg : 0 ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hprod_bound :
      ((radical n : ℕ) : ℝ) * ((radical (n + 2) : ℕ) : ℝ) * ((radical (n + 1) : ℕ) : ℝ)
        ≤ Real.sqrt ((n : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)
            * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    have h12 : ((radical n : ℕ) : ℝ) * ((radical (n + 2) : ℕ) : ℝ)
        ≤ Real.sqrt ((n : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ) :=
      mul_le_mul hrn hrn2 hr2_nonneg hs_nonneg
    have hr12_nonneg :
        0 ≤ Real.sqrt ((n : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ) := by positivity
    exact mul_le_mul h12 hrn1 hr1_nonneg hr12_nonneg
  -- Step 4: bound by (n + 2)^{3/2}.
  have hsqrt_bound : Real.sqrt ((n : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)
        * Real.sqrt ((n + 1 : ℕ) : ℝ)
      ≤ ((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
    -- Each √m ≤ √(n+2), so product ≤ (√(n+2))^3 = (n+2)^{3/2}.
    have hn_le : ((n : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n ≤ n + 2)
    have hn1_le : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ n + 2)
    have hn2_le : ((n + 2 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := le_refl _
    have hsqrt_n_le := Real.sqrt_le_sqrt hn_le
    have hsqrt_n1_le := Real.sqrt_le_sqrt hn1_le
    have hsqrt_n2_le := Real.sqrt_le_sqrt hn2_le
    -- product ≤ (√(n+2))^3
    have hprod_le : Real.sqrt ((n : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)
            * Real.sqrt ((n + 1 : ℕ) : ℝ)
          ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)
            * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
      have h1 := mul_le_mul hsqrt_n_le hsqrt_n2_le hs2_nonneg hs2_nonneg
      have h12_nonneg :
          0 ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
        positivity
      exact mul_le_mul h1 hsqrt_n1_le hs1_nonneg h12_nonneg
    have hsq_cube : Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)
            * Real.sqrt ((n + 2 : ℕ) : ℝ)
          = ((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
      have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
      norm_num
    rw [hsq_cube] at hprod_le
    exact hprod_le
  -- Chain to get rad(prod) ≤ (n+2)^{3/2}.
  have hrad_chain :
      ((radical (n * (n + 2) * (n + 1) ^ 2) : ℕ) : ℝ)
        ≤ ((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
    (hrad_le_real.trans hprod_bound).trans hsqrt_bound
  -- Step 5: Plug into abc, raise to (1 + 1/4) = 5/4 power.
  have hK_pos : 0 < K := by
    -- Apply abc to (1, 1, 2): `2 ≤ K · rad(2)^{5/4} = K · 2^{5/4}`.
    have habc_triv := hK 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hrad2 : (radical (1 * 1 * 2 : ℕ) : ℕ) = 2 := by
      have h11 : (1 * 1 * 2 : ℕ) = 2 := by norm_num
      rw [h11]
      have h2 : Prime (2 : ℕ) := Nat.prime_two.prime
      exact_mod_cast UniqueFactorizationMonoid.radical_of_prime h2
    rw [hrad2] at habc_triv
    have hpos_pow : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ (1 + (1/4 : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2le : (2 : ℝ) ≤ K * ((2 : ℕ) : ℝ) ^ (1 + (1/4 : ℝ)) := by
      exact_mod_cast habc_triv
    nlinarith
  have hrad_chain_nn : 0 ≤ ((radical (n * (n + 2) * (n + 1) ^ 2) : ℕ) : ℝ) := by positivity
  have hn2_pos_real : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn2_pos
  have hpow_mono :
      ((radical (n * (n + 2) * (n + 1) ^ 2) : ℕ) : ℝ) ^ (1 + (1/4 : ℝ))
        ≤ (((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) ^ (1 + (1/4 : ℝ)) :=
    Real.rpow_le_rpow hrad_chain_nn hrad_chain (by norm_num)
  -- Simplify ((n+2)^(3/2))^(5/4) = (n+2)^(15/8).
  have hsimp_exp : (((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) ^ (1 + (1/4 : ℝ))
      = ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := by
    rw [← Real.rpow_mul (le_of_lt hn2_pos_real)]
    ring_nf
  rw [hsimp_exp] at hpow_mono
  have hk' : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := by
    have hLHS : (((n + 1 : ℕ) ^ 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [hLHS] at habc_app
    exact habc_app.trans (mul_le_mul_of_nonneg_left hpow_mono (le_of_lt hK_pos))
  -- Step 6: lower-bound (n+1)² ≥ (n+2)²/4.
  have hlower : ((n + 2 : ℕ) : ℝ) ^ 2 / 4 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h1 : ((n + 2 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      have : (n + 2 : ℕ) ≤ 2 * (n + 1) := by omega
      exact_mod_cast this
    have hpos : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by positivity
    nlinarith [sq_nonneg (((n + 2 : ℕ) : ℝ) - 2 * ((n + 1 : ℕ) : ℝ))]
  have hfinal : ((n + 2 : ℕ) : ℝ) ^ 2 / 4 ≤ K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) :=
    hlower.trans hk'
  -- Step 7: derive (n+2)^{1/8} ≤ 4K, then n + 2 ≤ (4K)^8.
  have hn2_pow_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) :=
    Real.rpow_pos_of_pos hn2_pos_real _
  have hsq_eq : ((n + 2 : ℕ) : ℝ) ^ 2 = ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  rw [hsq_eq] at hfinal
  -- Manipulate hfinal: (n+2)^2 / 4 ≤ K · (n+2)^{15/8}
  --   ⇒ (n+2)^{2 - 15/8} ≤ 4K
  --   ⇒ (n+2)^{1/8} ≤ 4K.
  have hkey : ((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤ 4 * K := by
    have h_2_15 : (2 : ℝ) - 15/8 = 1/8 := by norm_num
    -- From `hfinal : (n+2)^2 / 4 ≤ K · (n+2)^{15/8}`, multiply through by 4.
    have h4 : (0 : ℝ) < 4 := by norm_num
    have h₁ : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
        K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) * 4 := (div_le_iff₀ h4).mp hfinal
    have hfinal_mul : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
        (4 * K) * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := by
      have hring : K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) * 4 =
          (4 * K) * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := by ring
      calc ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)
          ≤ K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) * 4 := h₁
        _ = (4 * K) * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := hring
    have hdiv : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8)
        ≤ 4 * K := by
      rw [div_le_iff₀ hn2_pow_pos]
      calc ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)
          ≤ (4 * K) * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := hfinal_mul
        _ = 4 * K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := by ring
    rw [← Real.rpow_sub hn2_pos_real, h_2_15] at hdiv
    exact hdiv
  -- Raise both sides to the 8th power.
  have h4K_pos : 0 < 4 * K := by linarith
  have h_pow8 : ((n + 2 : ℕ) : ℝ) ≤ (4 * K) ^ (8 : ℕ) := by
    -- (n+2) = ((n+2)^{1/8})^8 ≤ (4K)^8.
    have h_lhs : (((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = ((n + 2 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) 8,
          ← Real.rpow_mul (le_of_lt hn2_pos_real)]
      norm_num
    have hnn : 0 ≤ ((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_nonneg (by positivity) _
    have h4K_nn : 0 ≤ (4 * K : ℝ) := by linarith
    have := pow_le_pow_left₀ hnn hkey 8
    rw [h_lhs] at this
    exact this
  -- Bound (4K)^8 ≤ (4|K| + 1)^8.
  have hbound :
      ((n + 2 : ℕ) : ℝ) ≤ (4 * |K| + 1) ^ (8 : ℕ) := by
    have h1 : (4 * K : ℝ) ≤ 4 * |K| + 1 := by
      have : K ≤ |K| := le_abs_self _
      linarith
    have h2 : (0 : ℝ) ≤ 4 * K := by linarith
    exact h_pow8.trans (pow_le_pow_left₀ h2 h1 8)
  -- Compare to N.
  have hbound_nat : (n + 2 : ℕ) ≤ N := by
    have hN_real : (4 * |K| + 1) ^ (8 : ℕ) ≤ (N : ℝ) := by
      simp only [hN_def, Nat.cast_add]
      have hceil_int : (4 * |K| + 1) ^ (8 : ℕ) ≤ (⌈(4 * |K| + 1) ^ (8 : ℕ)⌉ : ℝ) :=
        Int.le_ceil _
      have hceil_nn : (0 : ℝ) ≤ (⌈(4 * |K| + 1) ^ (8 : ℕ)⌉ : ℝ) := by
        have : (0 : ℝ) ≤ (4 * |K| + 1) ^ (8 : ℕ) := by positivity
        linarith
      have hceil_int_nn : (0 : ℤ) ≤ ⌈(4 * |K| + 1) ^ (8 : ℕ)⌉ := by
        exact_mod_cast hceil_nn
      have h_toNat : ((⌈(4 * |K| + 1) ^ (8 : ℕ)⌉.toNat : ℝ)) =
          ((⌈(4 * |K| + 1) ^ (8 : ℕ)⌉ : ℝ)) := by
        have := Int.toNat_of_nonneg hceil_int_nn
        exact_mod_cast this
      rw [h_toNat]
      linarith
    have : ((n + 2 : ℕ) : ℝ) ≤ (N : ℝ) := hbound.trans hN_real
    exact_mod_cast this
  omega

end ConsecutivePowerful
