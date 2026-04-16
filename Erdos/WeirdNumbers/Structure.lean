/-
# Structural Theorems for Weird Numbers

Key structural results about pseudoperfect and weird numbers:
1. Multiples of pseudoperfect numbers are pseudoperfect
2. Benkoski-Erdős: pn is weird when n is weird and p > σ(n)
-/
import Erdos.WeirdNumbers.Statement

namespace WeirdNumbers

/-- If d is a proper divisor of n and m ≥ 1, then m*d is a proper
    divisor of m*n. -/
theorem mul_properDivisor {m n d : ℕ} (hm : 0 < m) (hd : d ∈ n.properDivisors) :
    m * d ∈ (m * n).properDivisors := by
  rw [Nat.mem_properDivisors] at hd ⊢
  obtain ⟨hdn, hdn'⟩ := hd
  refine ⟨?_, ?_⟩
  · exact mul_dvd_mul_left m hdn
  · exact Nat.mul_lt_mul_of_pos_left hdn' hm

/-- **Multiples of pseudoperfect numbers are pseudoperfect.**

    If n is pseudoperfect (some subset of its proper divisors sums to n)
    and m ≥ 1, then m*n is pseudoperfect: multiply each divisor in the
    subset by m.

    Contrapositive: if m*n is weird, then n is not pseudoperfect. -/
theorem pseudoperfect_mul {m n : ℕ} (hm : 0 < m) (hn : Pseudoperfect n) :
    Pseudoperfect (m * n) := by
  obtain ⟨S, hSsub, hSsum⟩ := hn
  rw [Finset.mem_powerset] at hSsub
  refine ⟨S.image (m * ·), Finset.mem_powerset.mpr ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact mul_properDivisor hm (hSsub hd)
  · have hinj : ∀ a ∈ S, ∀ b ∈ S, m * a = m * b → a = b :=
      fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hm hab
    have key : (S.image (m * ·)).sum id = m * S.sum id := by
      rw [Finset.sum_image hinj]
      exact Finset.mul_sum S id m |>.symm
    rw [key, hSsum]

/-- Corollary: if m*n is weird (hence not pseudoperfect), then n
    is not pseudoperfect either. -/
theorem not_pseudoperfect_of_mul_weird {m n : ℕ} (hm : 0 < m)
    (hw : Weird (m * n)) : ¬Pseudoperfect n := by
  intro hn
  exact hw.2 (pseudoperfect_mul hm hn)

/-! ### Benkoski-Erdős: pn is weird -/

/-- If d divides p*n and p does not divide d, with p prime,
    then d divides n. -/
private theorem dvd_of_dvd_prime_mul {d p n : ℕ} (hp : Nat.Prime p)
    (hpd : ¬(p ∣ d)) (hdpn : d ∣ p * n) : d ∣ n :=
  ((hp.coprime_iff_not_dvd.mpr hpd).symm).dvd_of_dvd_mul_left hdpn

/-- The sum of the p-divisible elements of S equals p times
    the sum of their p-quotients. -/
private theorem sum_filter_dvd_eq_mul {S : Finset ℕ} {p : ℕ} :
    (S.filter (p ∣ ·)).sum id = p * (S.filter (p ∣ ·)).sum (· / p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_filter] at hx
  change x = p * (x / p)
  have := Nat.div_mul_cancel hx.2
  linarith

/-- The sum of a Finset of positive naturals is 0 iff the set is empty. -/
private theorem sum_id_eq_zero_of_pos {S : Finset ℕ} (hS : ∀ x ∈ S, 0 < x)
    (hsum : S.sum id = 0) : S = ∅ := by
  rw [Finset.sum_eq_zero_iff] at hsum
  by_contra h
  obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty h
  have h1 := hS x hx
  have h2 := hsum x hx
  simp at h2; omega

/-- **Benkoski-Erdős: if n is weird, p > σ(n) is prime, p ∤ n, then pn is weird.**

    This is the fundamental construction showing weird numbers have
    positive density. Given any weird number n, there are infinitely
    many primes p > σ(n) coprime to n, and each gives a new weird number pn.

    The proof has two parts:
    1. pn is abundant: σ(pn) = (1+p)σ(n) ≥ (1+p)·2n > 2pn.
    2. pn is not pseudoperfect: for any candidate subset S, the elements
       not divisible by p sum to at most σ(n) < p, and divisibility by p
       forces this sum to 0, reducing to pseudoperfectness of n. -/
theorem weird_mul_prime {n p : ℕ} (hw : Weird n) (hp : Nat.Prime p)
    (hpn : ¬p ∣ n) (hpgt : n.divisors.sum id < p) :
    Weird (p * n) := by
  have hn_pos : 0 < n := hw.1.1
  have hp_pos : 0 < p := hp.pos
  have hn_ne : n ≠ 0 := by omega
  have hcop : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn
  -- σ(n) notation
  set σn := n.divisors.sum id with hσn_def
  -- σ(p) = 1 + p
  have hσp : p.divisors.sum id = 1 + p := by
    rw [hp.divisors, show ({1, p} : Finset ℕ) = insert 1 {p} from rfl]
    rw [Finset.sum_insert (show (1 : ℕ) ∉ ({p} : Finset ℕ) by
      simp only [Finset.mem_singleton]
      exact hp.one_lt.ne'.symm)]
    simp
  -- σ(pn) = σ(p) · σ(n) = (1+p) · σ(n) (multiplicativity for coprime)
  have hσpn : (p * n).divisors.sum id = (1 + p) * σn := by
    have h : (p * n).divisors.sum id = p.divisors.sum id * n.divisors.sum id :=
      hcop.sum_divisors_mul
    rw [hσp] at h; exact h
  -- σ(n) = properDivisors.sum + n
  have hσn_split : σn = n.properDivisors.sum id + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  -- n abundant: σ(n) ≥ 2n
  have hσn_ge : 2 * n ≤ σn := by linarith [hw.1.2]
  -- (1+p)σn ≥ 2pn (needed for ℕ subtraction)
  have hge_pn : p * n ≤ (1 + p) * σn := by nlinarith
  constructor
  · -- Part 1: p*n is abundant
    refine ⟨Nat.mul_pos hp_pos hn_pos, ?_⟩
    -- properDivisors(pn).sum + pn = σ(pn) = (1+p)σn
    have hpd : (p * n).properDivisors.sum id + p * n = (1 + p) * σn := by
      have h1 : (p * n).divisors.sum id =
        (p * n).properDivisors.sum id + p * n :=
        Nat.sum_divisors_eq_sum_properDivisors_add_self
      linarith
    -- Need: p*n ≤ properDivisors.sum, i.e., 2pn ≤ (1+p)σn
    -- From σn ≥ 2n: (1+p)σn ≥ (1+p)·2n = 2n + 2pn ≥ 2pn
    nlinarith
  · -- Part 2: p*n is not pseudoperfect
    intro ⟨S, hSmem, hSsum⟩
    rw [Finset.mem_powerset] at hSmem
    -- Split S by p-divisibility
    set S₀ := S.filter (fun d => ¬(p ∣ d))
    set S₁ := S.filter (p ∣ ·)
    -- Sum decomposition: S.sum = S₀.sum + S₁.sum
    have hS_split : S.sum id = S₀.sum id + S₁.sum id := by
      rw [← Finset.sum_filter_add_sum_filter_not S (p ∣ ·)]; ring
    -- S₁.sum = p * S₁.sum(·/p)
    have hS₁_eq : S₁.sum id = p * S₁.sum (· / p) := sum_filter_dvd_eq_mul
    -- Each element of S₀ divides n (coprime argument)
    have hS₀_dvd : ∀ d ∈ S₀, d ∣ n := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdpd := hSmem hd.1
      rw [Nat.mem_properDivisors] at hdpd
      exact dvd_of_dvd_prime_mul hp hd.2 hdpd.1
    -- S₀ ⊆ n.divisors, so S₀.sum ≤ σ(n)
    have hS₀_le : S₀.sum id ≤ σn := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd; exact Nat.mem_divisors.mpr ⟨hS₀_dvd d hd, hn_ne⟩
      · intro _ _ _; exact Nat.zero_le _
    -- S₀.sum + p * S₁.sum(·/p) = pn
    have hS_eq : S₀.sum id + p * S₁.sum (· / p) = p * n := by
      linarith
    -- p | S₀.sum (since S₀.sum = pn - p*(S₁.sum(·/p)))
    have hp_dvd : p ∣ S₀.sum id := by
      have hle : S₁.sum (· / p) ≤ n := by
        by_contra hc; push_neg at hc
        have := Nat.mul_lt_mul_of_pos_left hc hp_pos
        linarith [Nat.zero_le (S₀.sum id)]
      refine ⟨n - S₁.sum (· / p), ?_⟩
      zify [hle] at hS_eq ⊢
      linarith
    -- S₀.sum < p (since S₀.sum ≤ σn < p)
    -- Combined with p | S₀.sum: S₀.sum = 0
    have hS₀_zero : S₀.sum id = 0 := Nat.eq_zero_of_dvd_of_lt hp_dvd (by omega)
    -- S₀ = ∅ (all elements of properDivisors(pn) are positive)
    have hS₀_empty : S₀ = ∅ := by
      apply sum_id_eq_zero_of_pos _ hS₀_zero
      intro x hx
      have := hSmem (Finset.mem_of_mem_filter x hx)
      rw [Nat.mem_properDivisors] at this
      exact Nat.pos_of_dvd_of_pos this.1 (Nat.mul_pos hp_pos hn_pos)
    -- Therefore S₁.sum(·/p) = n
    have hT_sum : S₁.sum (· / p) = n := by
      have h1 : p * S₁.sum (· / p) = p * n := by linarith [hS₀_zero]
      exact Nat.eq_of_mul_eq_mul_left hp_pos h1
    -- Build pseudoperfect witness for n
    -- T = S₁.image (·/p) ⊆ properDivisors(n) with T.sum id = n
    have : Pseudoperfect n := by
      set T := S₁.image (· / p)
      have hT_sub : T ⊆ n.properDivisors := by
        intro e he
        rw [Finset.mem_image] at he
        obtain ⟨d, hd, rfl⟩ := he
        rw [Finset.mem_filter] at hd
        have hdS := hSmem hd.1
        rw [Nat.mem_properDivisors] at hdS ⊢
        have hpd := hd.2  -- p ∣ d
        constructor
        · -- d/p | n: d = p*(d/p) | p*n, so p*(d/p) | p*n, hence d/p | n
          have h1 : p * (d / p) = d := by rw [mul_comm]; exact Nat.div_mul_cancel hpd
          have h2 : p * (d / p) ∣ p * n := by rw [h1]; exact hdS.1
          exact (mul_dvd_mul_iff_left (show p ≠ 0 by omega)).mp h2
        · -- d/p < n: d < pn so d/p < n
          exact Nat.div_lt_of_lt_mul hdS.2
      have hinj : ∀ a ∈ S₁, ∀ b ∈ S₁, a / p = b / p → a = b := by
        intro a ha b hb hab
        rw [Finset.mem_filter] at ha hb
        have h1 := Nat.div_mul_cancel ha.2  -- a/p * p = a
        have h2 := Nat.div_mul_cancel hb.2  -- b/p * p = b
        calc a = a / p * p := h1.symm
          _ = b / p * p := by rw [hab]
          _ = b := h2
      have hT_sum' : T.sum id = n := by
        rw [Finset.sum_image hinj]; exact hT_sum
      exact ⟨T, Finset.mem_powerset.mpr hT_sub, hT_sum'⟩
    exact hw.2 this

/-! ### Infinitely many weird numbers -/

/-- Given any weird number, there exists a strictly larger weird number.
    This is an immediate consequence of `weird_mul_prime` and the infinitude
    of primes: pick any prime p > σ(n), which must be coprime to n since
    p > σ(n) ≥ 2n > n, and then pn is weird. -/
theorem weird_exists_gt (n : ℕ) (hw : Weird n) : ∃ m, n < m ∧ Weird m := by
  set σn := n.divisors.sum id
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (σn + 1)
  have hpσ : σn < p := by omega
  have hn_pos := hw.1.1
  have hσ_split : σn = n.properDivisors.sum id + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hσn_ge : 2 * n ≤ σn := by linarith [hw.1.2]
  have hpn : ¬p ∣ n := by
    intro hpd
    have : p ≤ n := Nat.le_of_dvd hn_pos hpd
    linarith
  refine ⟨p * n, ?_, weird_mul_prime hw hp hpn hpσ⟩
  nlinarith [hp.two_le]

/-- **There are infinitely many weird numbers.**

    Starting from the smallest weird number 70 and repeatedly applying
    `weird_exists_gt`, we obtain weird numbers exceeding any bound. -/
theorem infinitely_many_weird : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Weird n := by
  suffices h : ∀ N, ∃ n, N ≤ n ∧ Weird n from
    fun N => let ⟨n, hn, hw⟩ := h (N + 1); ⟨n, by omega, hw⟩
  intro N
  induction N with
  | zero => exact ⟨70, by omega, seventy_is_weird⟩
  | succ N ih =>
    obtain ⟨n, hn, hw⟩ := ih
    by_cases h : N + 1 ≤ n
    · exact ⟨n, h, hw⟩
    · -- n = N, so use weird_exists_gt to get a bigger one
      obtain ⟨m, hm, hwm⟩ := weird_exists_gt n hw
      exact ⟨m, by omega, hwm⟩

end WeirdNumbers
