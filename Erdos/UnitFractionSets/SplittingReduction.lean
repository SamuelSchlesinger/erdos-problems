/-
# Erdős Problem 301: The Splitting-Route Reduction Layer

This file isolates the **reduction layer** of the "splitting route" toward the
conjectured threshold of Erdős Problem #301: the maximum density of a
unit-fraction sum-free set `A ⊆ {1,…,N}` is conjectured to be `(1/2 + o(1))N`.

## The splitting route, in one paragraph

If repeated denominators were allowed, "bad" would reduce to plain divisibility:
when `a ∣ b` in `A` one may write `1/a = (b/a)·(1/b)`. The largest set avoiding all
divisibility (a *primitive* set) has size `≤ ⌈N/2⌉`, because the largest-odd-divisor
map `oddpart(n) = ordCompl[2] n` is injective on any primitive set and there are
exactly `⌈N/2⌉` odd numbers in `[1,N]`. Hence density `> 1/2` *forces* a
repeated-denominator obstruction. Problem #301 demands **distinct** denominators,
which kills that easy obstruction; the route "splits" the forced repeated
obstruction into distinct unit fractions drawn from `A`, using `A`'s density as a
reservoir. The analytic heart of that splitting is a targeted Egyptian
representation — the Bloom–Mehta circle-method wall.

## What this file proves (sorry-free) and what it does not

* **Lemma 1 — divisor supersaturation** (`card_gt_half_implies_dvd_pair`): a
  genuine standalone result. If `A ⊆ {1,…,N}` and `|A| > ⌈N/2⌉ = (N+1)/2`, then
  `A` contains a pair `a ∣ b` with `a < b`. Proof: oddpart injection + pigeonhole.
  This is fully proved here.

* **The master reduction** (`sumFree_card_le_half_under_R`): conditional on the
  hypothesis `DensityForcesRep N`, every sum-free `A ⊆ {1,…,N}` satisfies
  `|A| ≤ ⌈N/2⌉`. The reduction itself is unconditional and sorry-free.

* **(R) = `DensityForcesRep N`** is the *sole* non-proved object. It is the
  analytic content (targeted Egyptian representation), gated on Bloom-type
  machinery. It is carried as an explicit hypothesis, **never** a `sorry`.

## Honest leverage accounting (do not oversell)

`DensityForcesRep N` is logically **equivalent** to the #301 upper bound at `N`:
the forward direction is `sumFree_card_le_half_under_R` and the converse is
`upperBound_implies_DensityForcesRep` (both proved below). So this file is a
faithful **restatement** of the target inequality, *not* a reduction that buys
logical leverage at the reduction layer. The genuine deliverables are
(a) Lemma 1, a standalone divisor-supersaturation result, and
(b) a clean, Bloom–Mehta-facing interface (`DensityForcesRep`, `witnessPool`,
`poolRep_contradicts_sumFree`) isolating exactly the analytic content that remains
open. Discharging `DensityForcesRep` *is* solving the open problem; no shortcut is
implied.

Reference: https://www.erdosproblems.com/301 (and b-mehta.github.io/unit-fractions
for the eventual analytic input).
-/
import Erdos.UnitFractionSets.Statement

namespace UnitFractionSets

/-- The *witness pool* for `a` inside `A`: the elements of `A` other than `a`
    that lie in `Icc 1 N`.

    This is `(A.erase a) ∩ Icc 1 N` — deliberately the SAME set that `SumFree`
    quantifies its witness `S` over (`S ⊆ A.erase a`), intersected with the
    ambient interval. Crucially it admits denominators both ABOVE and BELOW `a`,
    so a representation drawn from it is a faithful proxy for a genuine `SumFree`
    violation. (Contrast a `tail`-based design restricted to `b > a`, which would
    be a strictly stronger, non-faithful proxy.) For `A ⊆ Icc 1 N` the `Icc 1 N`
    factor is redundant but is kept so the hypothesis below reads as a
    self-contained statement. -/
def witnessPool (A : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  (A.erase a) ∩ Finset.Icc 1 N

/-- **Hypothesis (R), density-triggered single-witness form.**

    If `A ⊆ {1,…,N}` is *denser than the conjectured threshold*
    `⌈N/2⌉ = (N+1)/2`, then SOME element `a ∈ A` admits a targeted Egyptian
    representation `1/a = ∑_{b ∈ S} 1/b` with `S` a nonempty subset of `a`'s
    witness pool (distinct denominators, automatic since `S : Finset ℕ`).

    This is the sole non-proved object of the splitting route; proving it is the
    Bloom–Mehta circle-method wall, OUT OF SCOPE, carried as an explicit
    hypothesis, NEVER a `sorry`.

    HONEST FRAMING (do not oversell): the trigger is GLOBAL DENSITY of `A` and the
    conclusion is a SINGLE existential witness — NOT a per-element assertion. This
    is what makes the conditional reduction non-vacuous. The price is that
    `DensityForcesRep N` is LOGICALLY EQUIVALENT to the #301 upper bound at `N`
    (both directions proved: `sumFree_card_le_half_under_R` and
    `upperBound_implies_DensityForcesRep`), so it is a faithful RESTATEMENT of the
    target inequality, not a strictly weaker object that buys logical leverage at
    the reduction layer. The value delivered is (a) Lemma 1
    (`card_gt_half_implies_dvd_pair`), a genuine standalone result, and (b) a
    clean, Bloom–Mehta-facing interface isolating exactly the analytic content
    that remains. -/
def DensityForcesRep (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → (N + 1) / 2 < A.card →
    ∃ a ∈ A, ∃ S ⊆ witnessPool A N a, S.Nonempty ∧
      (∑ b ∈ S, (1 / b : ℚ)) = (1 / a : ℚ)

/-- **Lemma 1 — divisor supersaturation (one pair).** If `A ⊆ {1,…,N}` and
    `|A| > ⌈N/2⌉ = (N+1)/2`, then `A` contains a pair `a ∣ b` with `a < b`.

    This is a genuine standalone result and the intended mechanism by which a
    future proof of `DensityForcesRep` produces its witness: a dense `A` contains
    `a ∣ b` with `a < b`, and then `b ∈ witnessPool A N a` (since `b > a ≥ 1` and
    `b ≤ N`), supplying the nonempty subset from which the Egyptian
    representation must be built.

    PROOF. The largest-odd-divisor map `n ↦ ordCompl[2] n` sends `A` into the set
    `T` of odd numbers in `[1,N]`, which has `≤ (N+1)/2` elements (it injects into
    `Icc 1 ((N+1)/2)` via `m ↦ (m+1)/2`). Since `|A| > (N+1)/2 ≥ |T|`, pigeonhole
    yields distinct `x, y ∈ A` with the same odd part. Equal odd parts forces one
    to divide the other (their `2`-adic valuations are comparable), and the
    divisibility together with `x ≠ y` upgrades to a strict order. -/
theorem card_gt_half_implies_dvd_pair (N : ℕ) (A : Finset ℕ)
    (hAN : A ⊆ Finset.Icc 1 N) (hcard : (N + 1) / 2 < A.card) :
    ∃ a ∈ A, ∃ b ∈ A, a ∣ b ∧ a < b := by
  set T := (Finset.Icc 1 N).filter (fun n => Odd n) with hT
  have hcardIcc : (Finset.Icc 1 ((N+1)/2)).card = (N+1)/2 := by rw [Nat.card_Icc]; omega
  have hTcard : T.card ≤ (N+1)/2 := by
    rw [hT, ← hcardIcc]
    apply Finset.card_le_card_of_injOn (fun m => (m + 1) / 2)
    · intro m hm
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hm
      obtain ⟨⟨h1, h2⟩, k, hk⟩ := hm
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hx hy
      obtain ⟨_, kx, hkx⟩ := hx
      obtain ⟨_, ky, hky⟩ := hy
      simp only at hxy
      omega
  have hmaps : Set.MapsTo (fun n => ordCompl[2] n) (A : Set ℕ) (T : Set ℕ) := by
    intro n hn
    have hnIcc := hAN hn
    simp only [Finset.mem_Icc] at hnIcc
    have hn0 : n ≠ 0 := by omega
    simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.ordCompl_pos 2 hn0, le_trans (Nat.ordCompl_le n 2) hnIcc.2⟩, ?_⟩
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hlt : T.card < A.card := lt_of_le_of_lt hTcard hcard
  obtain ⟨x, hxA, y, hyA, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hxy : ordCompl[2] x = ordCompl[2] y := heq
  have hx := Nat.ordProj_mul_ordCompl_eq_self x 2
  have hy := Nat.ordProj_mul_ordCompl_eq_self y 2
  have hdvd : x ∣ y ∨ y ∣ x := by
    rcases le_total (x.factorization 2) (y.factorization 2) with hle | hle
    · left; rw [← hx, ← hy, hxy]; exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hle) _
    · right; rw [← hx, ← hy, hxy]; exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hle) _
  have hxIcc := hAN hxA
  have hyIcc := hAN hyA
  simp only [Finset.mem_Icc] at hxIcc hyIcc
  rcases hdvd with hxy_dvd | hyx_dvd
  · refine ⟨x, hxA, y, hyA, hxy_dvd, ?_⟩
    rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hxy_dvd) with h | h
    · exact h
    · exact absurd h hne
  · refine ⟨y, hyA, x, hxA, hyx_dvd, ?_⟩
    rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hyx_dvd) with h | h
    · exact h
    · exact absurd h (Ne.symm hne)

/-- A targeted representation drawn from `a`'s witness pool is exactly a `SumFree`
    violation. If `1/a = ∑_{b ∈ S} 1/b` for a nonempty `S ⊆ witnessPool A N a`,
    then `A` is not `SumFree`.

    PROOF. `witnessPool A N a ⊆ A.erase a` by projecting the first component of
    the intersection, so `S ⊆ A.erase a`. The hypothesis `hsum : ∑ = 1/a` is the
    reverse orientation of the `≠` in `SumFree`, so we feed `hsum.symm`. -/
theorem poolRep_contradicts_sumFree (A : Finset ℕ) (N a : ℕ) (ha : a ∈ A)
    (S : Finset ℕ) (hSsub : S ⊆ witnessPool A N a) (hSne : S.Nonempty)
    (hsum : (∑ b ∈ S, (1 / b : ℚ)) = (1 / a : ℚ)) :
    ¬ SumFree A := by
  intro hSF
  have hSerase : S ⊆ A.erase a := by
    intro b hb
    have hbpool := hSsub hb
    simp only [witnessPool, Finset.mem_inter] at hbpool
    exact hbpool.1
  exact hSF a ha S hSerase hSne hsum.symm

/-- **Master reduction (Lemma 2), non-vacuous form.** Conditional on the
    density-triggered targeted-representation hypothesis `DensityForcesRep N`,
    every sum-free set `A ⊆ {1,…,N}` has at most `⌈N/2⌉ = (N+1)/2` elements —
    density `≤ 1/2`, matching the conjectured Erdős #301 threshold. The ONLY
    non-proved input is `DensityForcesRep N`; the reduction itself is
    unconditional and `sorry`-free.

    This bound is NON-VACUOUS: it is achieved with equality on `Icc (N/2+1) N`
    (the proven `SumFree` lower-bound set `upper_half_sum_free`), not collapsed to
    `|A| ≤ 1`. See the module docstring and `upperBound_implies_DensityForcesRep`
    for the honest accounting that `DensityForcesRep N` is logically EQUIVALENT to
    this very bound.

    Lemma 1 (`card_gt_half_implies_dvd_pair`) is NOT on the critical path here —
    the density trigger feeds `hR` directly. Lemma 1 is retained as a standalone
    result and as the intended mechanism by which a future proof of
    `DensityForcesRep` produces its witness. -/
theorem sumFree_card_le_half_under_R (N : ℕ) (A : Finset ℕ)
    (hR : DensityForcesRep N) (hSF : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card ≤ (N + 1) / 2 := by
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨a, haA, S, hSsub, hSne, hsum⟩ := hR A hAN hgt
  exact poolRep_contradicts_sumFree A N a haA S hSsub hSne hsum hSF

/-- **Honesty lemma (converse of the reduction).** The #301 upper bound at `N`
    implies `DensityForcesRep N`, establishing that `DensityForcesRep N` is
    logically EQUIVALENT to that upper bound (the forward direction is
    `sumFree_card_le_half_under_R`). Therefore the carried hypothesis adds no
    logical leverage at the reduction layer — it is a faithful restatement of the
    target inequality.

    PROOF. Density `> ⌈N/2⌉` and the upper bound `hUB` force `¬ SumFree A`
    (contrapositive). Unfolding `¬ SumFree A` yields exactly a witness
    `a ∈ A`, `S ⊆ A.erase a`, `S.Nonempty`, `1/a = ∑`. We repackage `S` into
    `witnessPool A N a` using `A ⊆ Icc 1 N`, and flip the equation orientation
    with `hsum.symm`. -/
theorem upperBound_implies_DensityForcesRep (N : ℕ)
    (hUB : ∀ A : Finset ℕ, SumFree A → A ⊆ Finset.Icc 1 N → A.card ≤ (N + 1) / 2) :
    DensityForcesRep N := by
  intro A hAN hgt
  have hnotSF : ¬ SumFree A := by
    intro hSF
    have := hUB A hSF hAN
    omega
  unfold SumFree at hnotSF
  push Not at hnotSF
  obtain ⟨a, haA, S, hSerase, hSne, hsum⟩ := hnotSF
  refine ⟨a, haA, S, ?_, hSne, hsum.symm⟩
  intro b hb
  simp only [witnessPool, Finset.mem_inter]
  exact ⟨hSerase hb, hAN (Finset.mem_of_mem_erase (hSerase hb))⟩

end UnitFractionSets
