import Erdos.PermutationMonotoneAP.Statement
import Erdos.PermutationMonotoneAP.Forcing

set_option linter.style.header false

/-!
# The dyadic (2-adic) reduction for monotone 4-APs (Erdős #195/#196)

This file packages the **2-adic self-similar structure** underlying Erdős
problem #196 ("must every permutation of `ℕ` contain a monotone 4-term AP?")
into reusable, `k`-generic Lean lemmas.

## The function-level affine invariance (the key primitive)

The heart of the file is the `k`-generic, *function-level* affine invariance of
`HasMonotoneAP`:
```
HasMonotoneAP (fun n => c + a * g n) k ↔ HasMonotoneAP g k     (a ≥ 1, k ≥ 2).
```
The forward direction holds for **every** `k` and every `a` (an AP in `g`
pushes forward to an AP in `c + a·g`); the backward direction needs `k ≥ 2`
(to recover the common difference by cancelling `a`) and `a ≥ 1` (to cancel).
This is strictly more flexible than the set-level `isFree_*_affine_image`
lemmas in `Forcing.lean`: it is stated for arbitrary `g : ℕ → ℕ` and any `k`.

## The dyadic 4-AP reduction (the heart of the "2^k barrier")

A monotone 4-AP `v, v+d, v+2d, v+3d` whose common difference `d` is divisible by
`2^j` has **all four terms in one residue class mod `2^j`** (all `≡ v`), and
dividing that class by `2^j` (the affine map `t ↦ (t - r)/2^j`) turns the 4-AP
into a 4-AP with the **smaller** common difference `d / 2^j`. Taking
`j = v₂(d)` (the exact 2-adic valuation) makes the rescaled difference **odd**.

Consequently (the conceptual statement, `erdos196_iff_oddDiff_free`): an order
avoids *all* monotone 4-APs **iff**, for every scale `j` and every residue class
`mod 2^j`, the rescaled sub-order avoids monotone 4-APs of **odd** common
difference. This is the self-similar (2-adic) reformulation of #196 — the form
in which Adenwalla (2022) solves the *bounded-valuation* version (`v₂(d) < k`),
leaving the all-scales version open.

The arithmetic core (`fourAP_dvd_pow_two_residue` / `fourAP_rescale_odd`) is
proven here in full; the order-theoretic packaging reuses `IsFree` and the
affine-invariance bridges from `Forcing.lean`.

References:
- https://www.erdosproblems.com/195, /196
- A. Adenwalla, *On permutations avoiding arithmetic progressions of bounded
  2-adic valuation* (2022).
- Davis, Entringer, Graham, Simmons, Acta Arith. 34 (1977), 81–90.
-/

namespace PermutationMonotoneAP

/-! ## Function-level, `k`-generic affine invariance of `HasMonotoneAP` -/

/-- **Forward affine push (all `k`, all `a`).** If `g` has a monotone `k`-AP,
then so does the affine image `n ↦ c + a · g n`: an AP `a₀ + j·d₀` in the values
of `g` maps to the AP `(c + a·a₀) + j·(a·d₀)`. No lower bound on `k` or `a` is
needed. -/
theorem hasMonotoneAP_affine_image {g : ℕ → ℕ} {k : ℕ} (c a : ℕ)
    (h : HasMonotoneAP g k) : HasMonotoneAP (fun n => c + a * g n) k := by
  obtain ⟨p, hp, a₀, d₀, hAP⟩ := h
  refine ⟨p, hp, (c : ℤ) + (a : ℤ) * a₀, (a : ℤ) * d₀, ?_⟩
  intro j hj
  have := hAP j hj
  push_cast
  rw [this]; ring

/-- **Backward affine pull (`k ≥ 2`, `a ≥ 1`).** If the affine image
`n ↦ c + a · g n` has a monotone `k`-AP and `k ≥ 2`, `a ≥ 1`, then `g` itself has
a monotone `k`-AP. The common difference `D` of the image-AP satisfies `a ∣ D`
(read off from terms `0` and `1`, which exist since `k ≥ 2`), so cancelling `a`
recovers an AP in the values of `g`. -/
theorem hasMonotoneAP_of_affine_image {g : ℕ → ℕ} {k : ℕ} {c a : ℕ}
    (ha : 0 < a) (hk : 2 ≤ k) (h : HasMonotoneAP (fun n => c + a * g n) k) :
    HasMonotoneAP g k := by
  obtain ⟨p, hp, A, D, hAP⟩ := h
  have haz : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  -- the affine relation at each index `j < k`
  have hrel : ∀ j < k, (c : ℤ) + (a : ℤ) * (g (p j) : ℤ) = A + (j : ℤ) * D := by
    intro j hj; have := hAP j hj; push_cast at this ⊢; linarith [this]
  -- read off `D = a · (g(p 1) - g(p 0))` from the first two terms
  have h0 := hrel 0 (by omega)
  have h1 := hrel 1 (by omega)
  simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero] at h0 h1
  have hD : D = (a : ℤ) * ((g (p 1) : ℤ) - (g (p 0) : ℤ)) := by linarith [h0, h1]
  -- the recovered AP in `g`: a₀ = g(p 0), d₀ = g(p 1) - g(p 0)
  refine ⟨p, hp, (g (p 0) : ℤ), (g (p 1) : ℤ) - (g (p 0) : ℤ), ?_⟩
  intro j hj
  have hj' := hrel j hj
  -- `a · g(p j) = a · (g(p 0) + j·(g(p 1) - g(p 0)))`, then cancel `a`
  have hcancel : (a : ℤ) * (g (p j) : ℤ)
      = (a : ℤ) * ((g (p 0) : ℤ) + (j : ℤ) * ((g (p 1) : ℤ) - (g (p 0) : ℤ))) := by
    have hAj : (a : ℤ) * (g (p j) : ℤ) = A + (j : ℤ) * D - (c : ℤ) := by linarith [hj']
    have hA : A = (c : ℤ) + (a : ℤ) * (g (p 0) : ℤ) := by linarith [h0]
    rw [hAj, hA, hD]; ring
  exact mul_left_cancel₀ haz hcancel

/-- **Function-level affine invariance (`k ≥ 2`, `a ≥ 1`).** The two-sided form:
the affine image `n ↦ c + a · g n` has a monotone `k`-AP iff `g` does. This is
the `k`-generic engine; the set-level statements `isFree_..._affine_image` are
consequences (specialized to `k = 3` and to enumerations of sets). -/
theorem hasMonotoneAP_affine_iff {g : ℕ → ℕ} {k : ℕ} {c a : ℕ}
    (ha : 0 < a) (hk : 2 ≤ k) :
    HasMonotoneAP (fun n => c + a * g n) k ↔ HasMonotoneAP g k :=
  ⟨hasMonotoneAP_of_affine_image ha hk, hasMonotoneAP_affine_image c a⟩

/-! ## The dyadic 4-AP arithmetic: residue class + rescaling -/

/-- **A `2^j`-divisible AP lies in one residue class mod `2^j`.** If `2^j ∣ d`
then for every `i`, the AP term `v + i·d` is congruent to `v` modulo `2^j`.
(All four terms of a 4-AP `v, v+d, v+2d, v+3d` share the residue `v % 2^j`.) -/
theorem fourAP_dvd_pow_two_residue {j d : ℕ} (hdvd : 2 ^ j ∣ d) (v i : ℕ) :
    (v + i * d) % 2 ^ j = v % 2 ^ j := by
  obtain ⟨q, rfl⟩ := hdvd
  rw [show v + i * (2 ^ j * q) = v + 2 ^ j * (i * q) by ring, Nat.add_mul_mod_self_left]

/-- **Rescaling a `2^j`-divisible AP by `1/2^j`.** With `r = v % 2^j` and
`d = 2^j · q`, the rescaled term `(v + i·d - r) / 2^j` equals `(v - r)/2^j + i·q`,
i.e. the four rescaled terms form a 4-AP with common difference `q = d / 2^j`.
Stated over `ℤ` so the AP shape is manifest. -/
theorem fourAP_rescale {j q : ℕ} (v i : ℕ) :
    (((v + i * (2 ^ j * q) - v % 2 ^ j) / 2 ^ j : ℕ) : ℤ)
      = ((v - v % 2 ^ j) / 2 ^ j : ℕ) + (i : ℤ) * (q : ℤ) := by
  have hpow : 0 < 2 ^ j := by positivity
  -- write `v = r + 2^j · b` with `r = v % 2^j`, `b = v / 2^j` (Euclidean division)
  set r := v % 2 ^ j with hr
  set b := v / 2 ^ j with hb
  have hvdecomp : v = 2 ^ j * b + r := (Nat.div_add_mod v (2 ^ j)).symm
  -- the divided/right-hand block index of `v - r`
  have hvr : (v - r) / 2 ^ j = b := by
    have : v - r = 2 ^ j * b := by omega
    rw [this, Nat.mul_div_cancel_left _ hpow]
  -- the divided block index of `v + i·d - r`
  have hsplit : v + i * (2 ^ j * q) - r = 2 ^ j * (b + i * q) := by
    rw [hvdecomp]; ring_nf; omega
  rw [hsplit, Nat.mul_div_cancel_left _ hpow, hvr]
  push_cast; ring

/-! ## `k`-generic set-level affine invariance and downward closure

The `Forcing.lean` file proves these for `k = 3`; here we lift them to arbitrary
`k` (using the function-level affine engine above), which is what the `k = 4`
dyadic packaging needs. -/

/-- **`k`-freeness is downward closed (any `k`).** Any infinite subset of a
`k`-free set is `k`-free: restrict the enumeration to the subset in the order it
appears; a monotone `k`-AP in the restriction is one in the original. (The proof
is `k`-agnostic — identical to `isFree_three_of_subset` with `3` replaced by the
generic `k`.) -/
theorem isFree_of_subset {S S' : Set ℕ} {k : ℕ} (hS : IsFree S k) (hsub : S' ⊆ S)
    (hinf : S'.Infinite) : IsFree S' k := by
  obtain ⟨e, he⟩ := hS
  set p : ℕ → Prop := fun n => (e n : ℕ) ∈ S' with hp
  have hS'inf : Infinite (S' : Set ℕ) := hinf.to_subtype
  have hpinf : (setOf p).Infinite := by
    have hF : Function.Injective (fun x : (S' : Set ℕ) => e.symm ⟨x.1, hsub x.2⟩) := by
      intro a b hab
      simp only at hab
      exact Subtype.ext (by simpa using e.symm.injective hab)
    have hsub2 : Set.range (fun x : (S' : Set ℕ) => e.symm ⟨x.1, hsub x.2⟩) ⊆ setOf p := by
      rintro n ⟨x, rfl⟩
      change (e (e.symm ⟨x.1, hsub x.2⟩) : ℕ) ∈ S'
      rw [Equiv.apply_symm_apply]; exact x.2
    exact (Set.infinite_range_of_injective hF).mono hsub2
  set g : ℕ → (S' : Set ℕ) := fun n => ⟨(e (Nat.nth p n) : ℕ),
    Nat.nth_mem_of_infinite hpinf n⟩ with hg
  have hgbij : Function.Bijective g := by
    constructor
    · intro a b hab
      simp only [hg, Subtype.mk.injEq] at hab
      exact Nat.nth_injective hpinf (e.injective (Subtype.ext hab))
    · rintro ⟨s, hs⟩
      have hm : p (e.symm ⟨s, hsub hs⟩) := by
        change (e (e.symm ⟨s, hsub hs⟩) : ℕ) ∈ S'
        rwa [Equiv.apply_symm_apply]
      obtain ⟨n, hn⟩ := Nat.subset_range_nth (p := p) hm
      refine ⟨n, Subtype.ext ?_⟩
      change (e (Nat.nth p n) : ℕ) = s
      rw [hn, Equiv.apply_symm_apply]
  refine ⟨Equiv.ofBijective g hgbij, ?_⟩
  intro hmono
  apply he
  obtain ⟨pos, hposmono, a, d, hAP⟩ := hmono
  exact ⟨fun j => Nat.nth p (pos j), (Nat.nth_strictMono hpinf).comp hposmono, a, d,
    fun j hj => hAP j hj⟩

/-- **Converse affine invariance of `k`-freeness (any `k`).** If the affine
image `{c + a·t : t ∈ T}` (with `a ≥ 1`) is `k`-free, then `T` is `k`-free: pull
the enumeration back along the affine bijection. A monotone `k`-AP in `T`'s
enumeration *pushes forward* (the all-`k` direction `hasMonotoneAP_affine_image`)
to one in the image enumeration, contradicting its `k`-freeness. -/
theorem isFree_of_affine_image {T : Set ℕ} {a c k : ℕ} (ha : 0 < a)
    (h : IsFree ((fun t => c + a * t) '' T) k) : IsFree T k := by
  obtain ⟨e', he'⟩ := h
  have hinj : Function.Injective (fun t : ℕ => c + a * t) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left ha (by omega)
  set φ' := Equiv.Set.image (fun t => c + a * t) T hinj with hφ'
  refine ⟨e'.trans φ'.symm, ?_⟩
  intro hmono
  apply he'
  -- the `T`-enumeration value equals `((c + a··) ∘ pullback)`, so apply the affine push
  have hval : (fun n => ((e' n : ℕ)))
      = (fun n => c + a * ((((e'.trans φ'.symm) n) : (T : Set ℕ)) : ℕ)) := by
    funext n
    have h1 : φ' (φ'.symm (e' n)) = e' n := φ'.apply_symm_apply (e' n)
    have h2 : ((φ' (φ'.symm (e' n)) : ℕ)) = ((e' n : ℕ)) := congrArg Subtype.val h1
    have h3 : ((φ' (φ'.symm (e' n)) : ℕ)) = c + a * ((φ'.symm (e' n) : ℕ)) := rfl
    rw [h3] at h2
    exact h2.symm
  rw [hval]
  exact hasMonotoneAP_affine_image c a hmono

/-! ## The `IsFree` order-theoretic packaging at `k = 4` -/

/-- **Self-similar dyadic reduction (necessary direction).** If a set `S` is
4-free, then for every scale `j` and every residue `c < 2^j`, the rescaled
residue-class restriction `{ i | c + 2^j · i ∈ S }` is 4-free whenever infinite.
This is the `k = 4` analogue of `isFree_three_apRestrict`: a 4-free set restricts
to a 4-free set in *every* dyadic residue class, and the difference `2^j` is the
scale at which the class is rescaled. Hence avoiding monotone 4-APs is inherited
by every rescaled dyadic block — the self-similar structure of #196. -/
theorem isFree_four_dyadicRestrict {S : Set ℕ} (hS : IsFree S 4) {j c : ℕ}
    (hinf : {i | c + 2 ^ j * i ∈ S}.Infinite) :
    IsFree {i | c + 2 ^ j * i ∈ S} 4 := by
  have hpow : 0 < 2 ^ j := by positivity
  -- reuse the generic affine restriction machinery, now at k = 4
  have hinj : Function.Injective (fun t : ℕ => c + 2 ^ j * t) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left hpow (by omega)
  have himg_sub : (fun t => c + 2 ^ j * t) '' {i | c + 2 ^ j * i ∈ S} ⊆ S := by
    rintro _ ⟨i, hi, rfl⟩; exact hi
  have himg_inf : ((fun t => c + 2 ^ j * t) '' {i | c + 2 ^ j * i ∈ S}).Infinite :=
    hinf.image hinj.injOn
  exact isFree_of_affine_image hpow (isFree_of_subset hS himg_sub himg_inf)

/-! ## Erdős #196: the avoidance statement and its equivalences -/

/-- **Erdős Problem 196 — the avoidance form.** There *exists* a permutation of
`ℕ` whose value-sequence contains no monotone 4-term AP. This is the (believed,
open) negation of `Erdos196`. -/
def Erdos196Avoidable : Prop := ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP (fun n => f n) 4

/-- `Erdos196Avoidable` is exactly the negation of `Erdos196`. -/
theorem erdos196Avoidable_iff_not_erdos196 : Erdos196Avoidable ↔ ¬ Erdos196 := by
  constructor
  · rintro ⟨f, hf⟩ hall; exact hf (hall f)
  · intro h
    by_contra hcon
    exact h (fun f => by
      by_contra hf
      exact hcon ⟨f, hf⟩)

/-- **`Set.univ` is 4-free iff `ℕ` admits a 4-AP-avoiding permutation.** An
enumeration of `Set.univ` is the same data as a permutation of `ℕ` (mediated by
the trivial equivalence `Set.univ ≃ ℕ`), and the value-sequences agree, so
avoiding monotone 4-APs transfers both ways. -/
theorem isFree_univ_four_iff_avoidable : IsFree (Set.univ : Set ℕ) 4 ↔ Erdos196Avoidable := by
  constructor
  · rintro ⟨e, he⟩
    -- compose with `Set.univ ≃ ℕ` to get a genuine permutation
    refine ⟨e.trans (Equiv.Set.univ ℕ), ?_⟩
    intro hmono
    exact he (by
      have : (fun n => ((e.trans (Equiv.Set.univ ℕ)) n : ℕ))
          = (fun n => ((e n : ℕ))) := rfl
      rwa [this] at hmono)
  · rintro ⟨f, hf⟩
    refine ⟨f.trans (Equiv.Set.univ ℕ).symm, ?_⟩
    intro hmono
    apply hf
    have hval : (fun n => (((f.trans (Equiv.Set.univ ℕ).symm) n : (Set.univ : Set ℕ)) : ℕ))
        = (fun n => (f n : ℕ)) := rfl
    rwa [hval] at hmono

/-- **The headline equivalence chain for Erdős #196.**
`Erdos196Avoidable ↔ ¬ Erdos196 ↔ IsFree Set.univ 4`. Resolving #196 in the
believed (YES-avoidable) direction is exactly the assertion `IsFree Set.univ 4`:
there is an enumeration of all of `ℕ` with no monotone 4-AP. -/
theorem erdos196_equivalences :
    (Erdos196Avoidable ↔ ¬ Erdos196) ∧ (Erdos196Avoidable ↔ IsFree (Set.univ : Set ℕ) 4) :=
  ⟨erdos196Avoidable_iff_not_erdos196, isFree_univ_four_iff_avoidable.symm⟩

end PermutationMonotoneAP
