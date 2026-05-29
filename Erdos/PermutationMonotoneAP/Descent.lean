import Erdos.PermutationMonotoneAP.Statement

/-!
# Rank descent and the no-infinite-doubling-orbit theorem

A genuinely **global** (infinitary) consequence of 3-freeness, using that the rank
function of an enumeration is a well-order of type `ω` (no infinite descent) — the
structure that *every* finite-window / local argument provably misses (finite sets are
always 3-free-orderable).

Fix a 3-free enumeration `e : ℕ ≃ S` and let `a = e 0` be the first-placed value (the
global rank-minimum). For any `x ∈ S` with `x > a` and the reflection `2x − a ∈ S`, the
progression `(a, x, 2x − a)` is a 3-term AP with **midpoint `x`**. Since `a` is rank-
minimal, `x` cannot be rank-median, so it must be rank-*maximal*, forcing `2x − a` to be
enumerated strictly before `x`:

> `rank (2x − a) < rank x`   (`rank_descent`).

Iterating the doubling map `T(x) = 2x − a` (so `Tᵏ(x) = a + 2ᵏ (x − a)`) produces a
strictly rank-*decreasing* sequence whenever the orbit stays inside `S`. As `ℕ` admits no
infinite strictly-decreasing sequence, **`S` cannot contain a full doubling orbit**
(`no_infinite_doubling_orbit`): for every `x ∈ S` with `x > a`, some `a + 2ᵏ (x − a) ∉ S`.

This is the cleanest invariant that genuinely *requires* the `ω` order type. It is,
however, only a **density-0** obstruction (each doubling orbit is exponentially sparse),
so it does not by itself bound `α(3)` / `β(3)` — matching the frontier analysis that a
density bound needs a stronger global object than rank descent alone.
-/

namespace PermutationMonotoneAP

variable {S : Set ℕ}

/-- **Rank descent.** For a 3-free enumeration with first value `a = e 0`: if `x ∈ S`
exceeds `a` and the reflection `2x − a ∈ S`, then `2x − a` is enumerated strictly before
`x`. (The AP `(a, x, 2x − a)` has midpoint `x`; as `a` is rank-minimal, `x` is rank-
maximal, so `2x − a` precedes `x`.) -/
theorem rank_descent (e : ℕ ≃ S) (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3)
    {t : ℕ} (ht : (e 0 : ℕ) < (e t : ℕ))
    (hmem : 2 * (e t : ℕ) - (e 0 : ℕ) ∈ S) :
    e.symm ⟨2 * (e t : ℕ) - (e 0 : ℕ), hmem⟩ < t := by
  have h0t : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; exact absurd ht (lt_irrefl _)
    · exact h
  set a := (e 0 : ℕ) with ha
  set x := (e t : ℕ) with hx
  set b := 2 * x - a with hb
  set u := e.symm ⟨b, hmem⟩ with hu
  have hval_u : (e u : ℕ) = b := by rw [hu]; simp
  have hbx : x < b := by rw [hb]; omega
  by_contra hcon
  rw [not_lt] at hcon
  have hut : t < u := by
    rcases lt_or_eq_of_le hcon with h | h
    · exact h
    · exfalso; rw [← h] at hval_u; omega
  apply he
  refine ⟨fun j => match j with | 0 => 0 | 1 => t | (n + 2) => u + n, ?_,
          (a : ℤ), (x : ℤ) - (a : ℤ), ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact h0t
    | 1 => exact hut
    | (n + 2) => simp only; omega
  · intro j hj
    have hbcast : (b : ℤ) = 2 * (x : ℤ) - (a : ℤ) := by
      rw [hb, Nat.cast_sub (by omega : a ≤ 2 * x)]; push_cast; ring
    interval_cases j
    · simp [ha]
    · simp only; rw [hx]; push_cast; ring
    · simp only [Nat.add_zero, hval_u, hbcast]; push_cast; ring

/-- **No infinite doubling orbit.** For a 3-free enumeration with first value `a = e 0`,
no `x ∈ S` with `x > a` has its entire doubling orbit `{a + 2ᵏ (x − a) : k}` inside `S`:
some `a + 2ᵏ (x − a) ∉ S`. (Otherwise `rank_descent` yields an infinite strictly-
decreasing sequence of ranks in `ℕ`.) -/
theorem no_infinite_doubling_orbit (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3)
    {x : ℕ} (hx : (e 0 : ℕ) < x) :
    ¬ ∀ k : ℕ, (e 0 : ℕ) + 2 ^ k * (x - (e 0 : ℕ)) ∈ S := by
  intro hall
  set a := (e 0 : ℕ) with ha
  set o : ℕ → ℕ := fun k => a + 2 ^ k * (x - a) with ho
  have ho_succ : ∀ k, o (k + 1) = 2 * o k - a := by
    intro k
    have e3 : 2 ^ (k + 1) * (x - a) = 2 * (2 ^ k * (x - a)) := by rw [pow_succ]; ring
    simp only [ho]; rw [e3]; omega
  have ho_gt : ∀ k, a < o k := by
    intro k
    have : 0 < 2 ^ k * (x - a) :=
      Nat.mul_pos (pow_pos (by norm_num) k) (by omega)
    simp only [ho]; omega
  set g : ℕ → ℕ := fun k => e.symm ⟨o k, hall k⟩ with hg
  have hpos : ∀ k, (e (g k) : ℕ) = o k := by intro k; simp [hg]
  have hdesc : ∀ k, g (k + 1) < g k := by
    intro k
    have ht : a < (e (g k) : ℕ) := by rw [hpos k]; exact ho_gt k
    have heq : 2 * (e (g k) : ℕ) - a = o (k + 1) := by rw [hpos k]; exact (ho_succ k).symm
    have hmem' : 2 * (e (g k) : ℕ) - a ∈ S := heq ▸ hall (k + 1)
    have hlt := rank_descent e he ht hmem'
    simp only [← ha] at hlt
    have hrw : e.symm ⟨2 * (e (g k) : ℕ) - a, hmem'⟩ = g (k + 1) :=
      congrArg e.symm (Subtype.ext heq)
    rwa [hrw] at hlt
  -- infinite descent in ℕ: `g k + k ≤ g 0`, contradiction at `k = g 0 + 1`
  have hbound : ∀ k, g k + k ≤ g 0 := by
    intro k
    induction k with
    | zero => simp
    | succ i ih => have := hdesc i; omega
  have := hbound (g 0 + 1); omega

end PermutationMonotoneAP
