/-
# Conditional Finiteness of Consecutive Powerful Triples

The Erdős problem #364 asks whether there are any triples `(n, n+1, n+2)` of
consecutive powerful numbers. Even an *infinitude* result would be a major
advance; the rigid expectation is finiteness, perhaps even non-existence.

This file records the standard conditional result: **assuming the abc
conjecture, only finitely many such triples can exist.** The proof goes via:

1. The classical decomposition `n = a² b³` of powerful numbers
   (`powerful_iff_eq_square_mul_cube`).
2. The radical bound `rad(n)² ∣ n`, hence `rad(n) ≤ √n`, for powerful `n`
   (`radical_sq_dvd_of_powerful`, `radical_le_sqrt_of_powerful`).
3. Applied to the identity `1 + n(n+2) = (n+1)²`, the abc conjecture forces
   `n` bounded: the radical of the product is at most `√(n(n+1)(n+2))`, and
   `(n+1)²` grows like `n²`, so any sub-quadratic upper bound — which abc
   delivers for `ε < 1/3` — suffices.

## Main results

* `powerful_iff_eq_square_mul_cube`: a positive integer is powerful iff it can
  be written as `a² · b³` with `b` squarefree.
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

/-! ### Decomposition `n = a² b³` for powerful numbers.

For each prime `p ∣ n` with exponent `e`, we split the contribution into the
`a`-part and the `b`-part:

* If `e` is even, the `a`-part absorbs `p^(e/2)` and the `b`-part gets nothing.
* If `e` is odd, then `e ≥ 3` (since `n` is powerful), the `b`-part absorbs
  `p` and the `a`-part absorbs `p^((e-3)/2)`.

Thus `a²b³` reproduces `n` exactly, and `b` is squarefree (each prime appears
at most once in `b`).
-/

/-- The `b`-part in the standard powerful decomposition `n = a² b³`: the
product of those primes of `n` whose exponent in `n` is odd. -/
private noncomputable def bPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with n.factorization p % 2 = 1, p

/-- The `a`-part in the standard powerful decomposition `n = a² b³`. For each
prime `p` of `n` with exponent `e`, the cube part `b` absorbs a factor of `p`
exactly when `e` is odd; the square part carries everything else. -/
private noncomputable def aPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors,
    p ^ (if n.factorization p % 2 = 0 then n.factorization p / 2
         else (n.factorization p - 3) / 2)

/-- The `b`-part is squarefree (a product of distinct primes). -/
private lemma squarefree_bPart (n : ℕ) : Squarefree (bPart n) := by
  classical
  unfold bPart
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    -- Different primes are coprime, hence relatively prime in the UFM sense.
    have : Nat.Coprime p q := (Nat.coprime_primes hp' hq').mpr hpq
    exact (Nat.isCoprime_iff_coprime.mpr this).isRelPrime
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree

/-- Square of the `a`-part times cube of the `b`-part reconstructs `n` for
positive powerful `n`. -/
private lemma aPart_sq_mul_bPart_cube {n : ℕ} (hn : Powerful n) :
    aPart n ^ 2 * bPart n ^ 3 = n := by
  classical
  have hn0 : n ≠ 0 := hn.1.ne'
  -- Unfold both parts and combine into a single product over `n.primeFactors`.
  unfold aPart bPart
  -- `(∏ p^f p) ^ 2 = ∏ p^(2 * f p)`.
  rw [← Finset.prod_pow]
  -- `(∏ p ∈ filter, p) ^ 3 = ∏ p ∈ filter, p^3`.
  rw [← Finset.prod_pow]
  -- Extend the second product to all of `n.primeFactors` using indicator powers.
  have hbcube :
      (∏ p ∈ n.primeFactors with n.factorization p % 2 = 1, p ^ 3)
        = ∏ p ∈ n.primeFactors,
            p ^ (3 * (if n.factorization p % 2 = 1 then 1 else 0)) := by
    rw [show (∀ p ∈ n.primeFactors,
              p ^ (3 * (if n.factorization p % 2 = 1 then 1 else 0))
                = if n.factorization p % 2 = 1 then p ^ 3 else 1 from
            fun p _hp => by
              by_cases h : n.factorization p % 2 = 1
              · simp [h]
              · simp [h]) |> Finset.prod_congr rfl]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    rfl
  rw [hbcube, ← Finset.prod_mul_distrib]
  -- Now both products are over `n.primeFactors`. Combine the exponents.
  -- LHS prim form: ∏ p^(2 * (a-part exponent) + 3 * (b-part indicator)).
  -- Aim to match with `∏ p^(n.factorization p) = n`.
  have hn_eq : (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n := by
    have hprod : n.factorization.prod (· ^ ·) = n :=
      Nat.factorization_prod_pow_eq_self hn0
    rwa [Finsupp.prod, Nat.support_factorization] at hprod
  rw [← hn_eq]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [← pow_add]
  congr 1
  -- The exponent identity. Use that powerful means `n.factorization p ≥ 2`.
  have hpow : 2 ≤ n.factorization p :=
    ((powerful_iff_factorization_ge_two.mp hn).2 p hp)
  set e := n.factorization p
  rcases Nat.mod_two_eq_zero_or_one e with hmod | hmod
  · simp only [hmod]
    omega
  · simp only [hmod]
    omega

/-- **Squarefree-cube decomposition of powerful numbers.**

A positive natural number is powerful iff it can be written as `a²b³` with `b`
squarefree.

The forward implication uses the explicit decomposition: for each prime `p` of
`n` with exponent `e`, send a factor of `p` into `b` whenever `e` is odd
(forcing `e ≥ 3` because `n` is powerful) and the rest into `a`.

The reverse implication is direct: every prime of `a²b³` has exponent at least
`2`, since either `p ∣ a` (giving exponent `≥ 2`) or `p ∣ b` only (giving
exponent `3`, using squarefreeness of `b`). -/
theorem powerful_iff_eq_square_mul_cube {n : ℕ} (hn : 0 < n) :
    Powerful n ↔ ∃ a b : ℕ, n = a ^ 2 * b ^ 3 ∧ Squarefree b := by
  refine ⟨fun hpow => ⟨aPart n, bPart n, ?_, squarefree_bPart n⟩, ?_⟩
  · exact (aPart_sq_mul_bPart_cube hpow).symm
  · rintro ⟨a, b, hn_eq, _hb⟩
    refine ⟨hn, ?_⟩
    intro p hp hpdvd
    rw [hn_eq] at hpdvd ⊢
    rcases (hp.dvd_mul.mp hpdvd) with hpa | hpb
    · have hpa1 : p ∣ a := hp.dvd_of_dvd_pow hpa
      have : p ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd hpa1 2
      exact this.trans (dvd_mul_right _ _)
    · have hpb1 : p ∣ b := hp.dvd_of_dvd_pow hpb
      have h3 : p ^ 3 ∣ b ^ 3 := pow_dvd_pow_of_dvd hpb1 3
      have h2 : p ^ 2 ∣ p ^ 3 := pow_dvd_pow p (by norm_num)
      exact (h2.trans h3).trans (dvd_mul_left _ _)

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
  rw [radical_eq_prod_primeFactors, ← Finset.prod_pow]
  have hn_eq : (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n := by
    have hprod : n.factorization.prod (· ^ ·) = n :=
      Nat.factorization_prod_pow_eq_self hn0
    rwa [Finsupp.prod, Nat.support_factorization] at hprod
  rw [← hn_eq]
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro p hp
  have hpow : 2 ≤ n.factorization p :=
    ((powerful_iff_factorization_ge_two.mp hn).2 p hp)
  exact pow_dvd_pow p hpow

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
  have hradn_pos : 0 < (radical n : ℕ) := by
    exact_mod_cast (UniqueFactorizationMonoid.Nat.radical_pos n : 0 < (radical n : ℕ))
  have hradn1_pos : 0 < (radical (n + 1) : ℕ) := by
    exact_mod_cast (UniqueFactorizationMonoid.Nat.radical_pos (n + 1) : 0 < (radical (n + 1) : ℕ))
  have hradn2_pos : 0 < (radical (n + 2) : ℕ) := by
    exact_mod_cast (UniqueFactorizationMonoid.Nat.radical_pos (n + 2) : 0 < (radical (n + 2) : ℕ))
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
    push_cast
    rfl
  have hrn2 : ((radical (n + 2) : ℕ) : ℝ) ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    have := radical_le_sqrt_of_powerful hpn2
    convert this using 2
    push_cast
    rfl
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
    have hn_le : ((n : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ n + 2)
    have hn1_le : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ n + 2)
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
      have h12_nonneg : 0 ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ) := by positivity
      exact mul_le_mul h1 hsqrt_n1_le hs1_nonneg h12_nonneg
    have hsq_cube : Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)
            * Real.sqrt ((n + 2 : ℕ) : ℝ)
          = ((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
      have hpos : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by positivity
      rw [Real.sqrt_eq_rpow]
      rw [show ((((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) * (((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2))
              * (((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)))
            = ((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2 + (1 : ℝ) / 2) by
          rw [Real.rpow_add (by positivity), Real.rpow_add (by positivity)]
          ring]
      ring_nf
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
    have h2le : (2 : ℝ) ≤ K * ((2 : ℕ) : ℝ) ^ (1 + (1/4 : ℝ)) := by exact_mod_cast habc_triv
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
    have hfinal' : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ 4 * (K * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8)) := by
      linarith
    have hfinal'' : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
        (4 * K) * ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8) := by linarith
    have hdiv : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ ((15 : ℝ) / 8)
        ≤ 4 * K := (div_le_iff₀ hn2_pow_pos).mpr (by linarith)
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
      have hceil_int_nn : (0 : ℤ) ≤ ⌈(4 * |K| + 1) ^ (8 : ℕ)⌉ := by exact_mod_cast hceil_nn
      have h_toNat : ((⌈(4 * |K| + 1) ^ (8 : ℕ)⌉.toNat : ℝ)) =
          ((⌈(4 * |K| + 1) ^ (8 : ℕ)⌉ : ℝ)) := by
        rw [Int.toNat_of_nonneg hceil_int_nn]
        rfl
      rw [h_toNat]
      linarith
    have : ((n + 2 : ℕ) : ℝ) ≤ (N : ℝ) := hbound.trans hN_real
    exact_mod_cast this
  omega

end ConsecutivePowerful
