import Erdos.PermutationMonotoneAP.Statement

/-!
# The van der Corput order avoids monotone 3-term APs

The *van der Corput* (reverse-binary) order `vdcLt`: `x ≺ y` iff at the lowest
bit where `x` and `y` differ, `x` has bit `0` and `y` has bit `1`.

**Main theorem** (`vdc_middle_not_between`): for every 3-term arithmetic
progression `x, x+d, x+2d` (with `d ≥ 1`), the middle term `x+d` is `≺`-extreme
— never strictly between the two endpoints. Equivalently, the van der Corput
linear order on `ℕ` contains no monotone 3-term AP.

This is the clean 2-adic mechanism behind every positive-density 3-free
construction (it provides the within-block scrambling): at the lowest set bit
`v` of `d`, the endpoints `x, x+2d` share bit `v` while the middle `x+d` has the
opposite bit, and `vdcLt` is decided by exactly that lowest differing bit.

(Note: the van der Corput order is a *dense* order on `ℕ`, not an `ω`-order, so
this does not by itself give an `ω`-3-free permutation — consistent with the
Davis–Entringer–Graham–Simmons theorem.)
-/

namespace PermutationMonotoneAP

namespace VDC

/-- Adding a multiple of `2^(v+1)` does not change bits `0,…,v`. -/
theorem testBit_add_mul_two_pow (v i : ℕ) (hi : i < v + 1) (x k : ℕ) :
    Nat.testBit (x + 2 ^ (v + 1) * k) i = Nat.testBit x i := by
  have hmod : (x + 2 ^ (v + 1) * k) % 2 ^ (v + 1) = x % 2 ^ (v + 1) :=
    Nat.add_mul_mod_self_left x (2 ^ (v + 1)) k
  have h1 : Nat.testBit ((x + 2 ^ (v + 1) * k) % 2 ^ (v + 1)) i
      = Nat.testBit (x + 2 ^ (v + 1) * k) i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  have h2 : Nat.testBit (x % 2 ^ (v + 1)) i = Nat.testBit x i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [← h1, hmod, h2]

/-- The three key 2-adic facts about a 3-AP `x, x+d, x+2d`: with `v` the lowest
set bit of `d`, the endpoints `x` and `x+2d` agree on bits `0,…,v`, while the
middle `x+d` agrees on bits `< v` but has the opposite bit at `v`. -/
theorem ap_bits (x d : ℕ) (hd : 0 < d) :
    ∃ v : ℕ,
      (∀ i < v, Nat.testBit (x + d) i = Nat.testBit x i) ∧
      Nat.testBit (x + d) v = !Nat.testBit x v ∧
      (∀ i < v + 1, Nat.testBit (x + 2 * d) i = Nat.testBit x i) := by
  obtain ⟨v, m, hm_odd, hdeq⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  obtain ⟨k, hk⟩ := hm_odd
  have hdk : d = 2 ^ v + 2 ^ (v + 1) * k := by rw [hdeq, hk]; ring
  have hsplit : x + d = 2 ^ v + (x + 2 ^ (v + 1) * k) := by rw [hdk]; ring
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i hi
    rw [hsplit, Nat.testBit_two_pow_add_gt hi, testBit_add_mul_two_pow v i (by omega) x k]
  · rw [hsplit, Nat.testBit_two_pow_add_eq, testBit_add_mul_two_pow v v (by omega) x k]
  · intro i hi
    have h2d : x + 2 * d = x + 2 ^ (v + 1) * m := by rw [hdeq]; ring
    rw [h2d, testBit_add_mul_two_pow v i hi x m]

/-- The van der Corput (reverse-binary) strict order: `x ≺ y` iff at the lowest
bit where they differ, `x` has bit `0` and `y` has bit `1`. -/
def vdcLt (x y : ℕ) : Prop :=
  ∃ v, Nat.testBit x v = false ∧ Nat.testBit y v = true ∧
    ∀ i < v, Nat.testBit x i = Nat.testBit y i

/-- `m` is van der Corput *between* `a` and `b`. -/
def vdcBetween (a m b : ℕ) : Prop := (vdcLt a m ∧ vdcLt m b) ∨ (vdcLt b m ∧ vdcLt m a)

/-- `vdcLt` is irreflexive. -/
theorem vdcLt_irrefl (x : ℕ) : ¬ vdcLt x x := by
  rintro ⟨v, h0, h1, _⟩; rw [h0] at h1; simp at h1

/-- `vdcLt` is transitive: comparison is decided by the lowest differing bit, and
those propagate. -/
theorem vdcLt_trans {x y z : ℕ} (hxy : vdcLt x y) (hyz : vdcLt y z) : vdcLt x z := by
  obtain ⟨v, hxv, hyv, hlowv⟩ := hxy
  obtain ⟨w, hyw, hzw, hloww⟩ := hyz
  rcases lt_trichotomy v w with hvw | hvw | hvw
  · exact ⟨v, hxv, by rw [← hloww v hvw]; exact hyv,
      fun i hi => by rw [hlowv i hi, hloww i (hi.trans hvw)]⟩
  · subst hvw; rw [hyv] at hyw; simp at hyw
  · exact ⟨w, by rw [hlowv w hvw]; exact hyw, hzw,
      fun i hi => by rw [hlowv i (hi.trans hvw), hloww i hi]⟩

/-- `vdcLt` is total (trichotomous): distinct naturals are comparable. -/
theorem vdcLt_total {x y : ℕ} (hxy : x ≠ y) : vdcLt x y ∨ vdcLt y x := by
  classical
  have hex : ∃ v, Nat.testBit x v ≠ Nat.testBit y v := by
    by_contra h
    exact hxy (Nat.eq_of_testBit_eq fun i => not_not.mp fun hne => h ⟨i, hne⟩)
  set v := Nat.find hex with hvdef
  have hv : Nat.testBit x v ≠ Nat.testBit y v := Nat.find_spec hex
  have hlow : ∀ i < v, Nat.testBit x i = Nat.testBit y i :=
    fun i hi => not_ne_iff.mp (Nat.find_min hex hi)
  cases hx : Nat.testBit x v
  · cases hy : Nat.testBit y v
    · rw [hx, hy] at hv; exact absurd rfl hv
    · exact Or.inl ⟨v, hx, hy, hlow⟩
  · cases hy : Nat.testBit y v
    · exact Or.inr ⟨v, hy, hx, fun i hi => (hlow i hi).symm⟩
    · rw [hx, hy] at hv; exact absurd rfl hv

/-- Trichotomy in the usual `lt ∨ eq ∨ gt` form. Together with `vdcLt_irrefl`,
`vdcLt_trans`, `vdcLt_total` this shows the van der Corput order is a strict
total order on `ℕ` — and `vdc_middle_not_between` shows it contains no monotone
3-term AP. So `ℕ` admits a strict total (dense) order avoiding monotone 3-APs. -/
theorem vdcLt_trichotomous (x y : ℕ) : vdcLt x y ∨ x = y ∨ vdcLt y x :=
  (eq_or_ne x y).elim (fun h => Or.inr (Or.inl h))
    (fun h => (vdcLt_total h).elim Or.inl (fun h' => Or.inr (Or.inr h')))

/-- If `a, b` agree on all bits below `v` and differ at bit `v`, then `vdcLt a b`
is decided by bit `v`: it holds iff `a` has `0` there. -/
theorem vdcLt_iff_of_firstDiff {a b v : ℕ} (hlow : ∀ i < v, Nat.testBit a i = Nat.testBit b i)
    (hdiff : Nat.testBit a v ≠ Nat.testBit b v) :
    vdcLt a b ↔ Nat.testBit a v = false := by
  constructor
  · rintro ⟨w, haw, hbw, hlt⟩
    have hw : w = v := by
      rcases lt_trichotomy w v with h | h | h
      · exact absurd (hlow w h) (by rw [haw, hbw]; simp)
      · exact h
      · exact absurd (hlt v h) hdiff
    rwa [hw] at haw
  · intro ha0
    have hb1 : Nat.testBit b v = true := by
      by_contra hb
      simp only [Bool.not_eq_true] at hb
      rw [ha0, hb] at hdiff
      exact hdiff rfl
    exact ⟨v, ha0, hb1, hlow⟩

/-- **Van der Corput avoids monotone 3-APs.** For every 3-term AP `x, x+d, x+2d`
with `d ≥ 1`, the middle `x+d` is never van der Corput between the endpoints. -/
theorem vdc_middle_not_between (x d : ℕ) (hd : 0 < d) :
    ¬ vdcBetween x (x + d) (x + 2 * d) := by
  obtain ⟨v, hlow, hflip, hlow2⟩ := ap_bits x d hd
  have hxz_v : Nat.testBit x v = Nat.testBit (x + 2 * d) v := (hlow2 v (by omega)).symm
  -- x  vs  x+d : agree below v, differ at v
  have hxm_low : ∀ i < v, Nat.testBit x i = Nat.testBit (x + d) i := fun i hi => (hlow i hi).symm
  have hxm_diff : Nat.testBit x v ≠ Nat.testBit (x + d) v := by
    rw [hflip]; cases Nat.testBit x v <;> simp
  -- x+d  vs  x+2d : agree below v, differ at v
  have hmz_low : ∀ i < v, Nat.testBit (x + d) i = Nat.testBit (x + 2 * d) i := by
    intro i hi; rw [hlow i hi, hlow2 i (by omega)]
  have hmz_diff : Nat.testBit (x + d) v ≠ Nat.testBit (x + 2 * d) v := by
    rw [hflip, ← hxz_v]; cases Nat.testBit x v <;> simp
  -- decode the four comparisons in terms of bit v of x
  have hxm : vdcLt x (x + d) ↔ Nat.testBit x v = false := vdcLt_iff_of_firstDiff hxm_low hxm_diff
  have hmx : vdcLt (x + d) x ↔ Nat.testBit (x + d) v = false :=
    vdcLt_iff_of_firstDiff (fun i hi => (hxm_low i hi).symm) (fun h => hxm_diff h.symm)
  have hmz : vdcLt (x + d) (x + 2 * d) ↔ Nat.testBit (x + d) v = false :=
    vdcLt_iff_of_firstDiff hmz_low hmz_diff
  have hzm : vdcLt (x + 2 * d) (x + d) ↔ Nat.testBit (x + 2 * d) v = false :=
    vdcLt_iff_of_firstDiff (fun i hi => (hmz_low i hi).symm) (fun h => hmz_diff h.symm)
  rintro (⟨hx_m, hm_z⟩ | ⟨hz_m, hm_x⟩)
  · -- x ≺ x+d  and  x+d ≺ x+2d
    have e1 : Nat.testBit x v = false := hxm.mp hx_m
    have e2 : Nat.testBit (x + d) v = false := hmz.mp hm_z
    rw [hflip, e1] at e2; simp at e2
  · -- x+2d ≺ x+d  and  x+d ≺ x
    have e1 : Nat.testBit (x + d) v = false := hmx.mp hm_x
    have e2 : Nat.testBit (x + 2 * d) v = false := hzm.mp hz_m
    rw [hflip] at e1
    rw [← hxz_v] at e2
    rw [e2] at e1
    simp at e1

/-!
## Corollary: the van der Corput order has no monotone `k`-AP for any `k ≥ 3`

This is the heart of the **construction-side** analysis of Erdős #196/#195 (does a
permutation of `ℕ`/`ℤ` avoid all monotone 4-APs?). The 3-AP result already gives the
4-AP (and every-`k`-AP) result *for free*, by a one-line observation:

> A vdc-monotone `k`-AP, `k ≥ 3`, contains a vdc-monotone consecutive 3-AP
> `(x+jd, x+(j+1)d, x+(j+2)d)`, whose middle is vdc-*between* its endpoints —
> contradicting `vdc_middle_not_between`.

The underlying 2-adic mechanism is *uniform in `d`* — in particular it handles
common differences `d` with **arbitrarily high 2-adic valuation** `v₂(d)`, which is
exactly the open barrier in Adenwalla's partial constructions (those handle only
`v₂(d) < k`). At bit `v = v₂(d)` the AP terms alternate in bit `v` as
`c, c̄, c, c̄, …` (by index parity), and `vdcLt` is decided by that lowest differing
bit; so consecutive terms always *flip* across bit `v`, never producing a monotone
run of length `≥ 3`.

**The honest catch (why this does NOT resolve #196).** `vdcLt` is a *dense* strict
total order on `ℕ` (`vdcLt_trichotomous` + density: between any two there is a third)
— order type ≈ the dyadic rationals in `[0,1)`, **not** order type `ω`. A permutation
of `ℕ` requires order type `ω` (a least element, finite predecessor sets). The DEGS
3-AP forcing (`Descent.rank_descent`, `Statement.hasMonotoneAP_three`) uses the
*least element* of `ω` essentially, and indeed `ℕ`-permutations are forced to contain
a monotone 3-AP — while this dense order avoids *all* `k`-APs. So the entire content
of #196 is the **order-type gap** `ω` vs. dense: can the all-scales 2-adic avoidance
of `vdcLt` be realized at order type `ω`? This theorem isolates that gap precisely. -/

/-- **Van der Corput avoids monotone 4-APs.** For every 4-term AP `x, x+d, x+2d, x+3d`
(`d ≥ 1`), the four terms are never strictly vdc-monotone — neither
`x ≺ x+d ≺ x+2d ≺ x+3d` nor its reverse. (Immediate from `vdc_middle_not_between`:
the first three terms would be vdc-monotone, making `x+d` vdc-between `x` and `x+2d`.)

This is the cleanest form of the *positive*/construction side of Erdős #196: the
natural 2-adic order avoiding all monotone 4-APs (uniformly over `v₂(d)`) does exist
— but as a *dense* order, not an `ω`-permutation. -/
theorem vdc_no_monotone_fourAP (x d : ℕ) (hd : 0 < d) :
    ¬ ((vdcLt x (x + d) ∧ vdcLt (x + d) (x + 2 * d) ∧ vdcLt (x + 2 * d) (x + 3 * d)) ∨
       (vdcLt (x + 3 * d) (x + 2 * d) ∧ vdcLt (x + 2 * d) (x + d) ∧ vdcLt (x + d) x)) := by
  rintro (⟨h01, h12, _⟩ | ⟨_, h21, h10⟩)
  · exact vdc_middle_not_between x d hd (Or.inl ⟨h01, h12⟩)
  · exact vdc_middle_not_between x d hd (Or.inr ⟨h21, h10⟩)

/-- **Van der Corput avoids monotone APs of every length `k ≥ 3`.** Phrased on a
length-`k` chain of AP terms given by a vdc-monotone witness: if the consecutive AP
terms `r 0 ≺ r 1 ≺ ⋯` (or the reverse) are vdc-ordered, the first three already give
a vdc-between configuration, impossible. Stated for the increasing case applied to any
window; the contradiction comes from the first three terms only. -/
theorem vdc_no_monotone_triple_increasing (x d : ℕ) (hd : 0 < d)
    (h01 : vdcLt x (x + d)) (h12 : vdcLt (x + d) (x + 2 * d)) : False :=
  vdc_middle_not_between x d hd (Or.inl ⟨h01, h12⟩)

end VDC

end PermutationMonotoneAP
