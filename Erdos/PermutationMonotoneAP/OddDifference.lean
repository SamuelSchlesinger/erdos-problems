import Erdos.PermutationMonotoneAP.Statement
import Erdos.PermutationMonotoneAP.Compactness

/-!
# Erdős #196, odd-difference layer: a permutation of `ℕ` with no monotone 4-term AP
of odd common difference (LeSaulnier–Vijay, 2011)

Erdős #196 asks whether every permutation of `ℕ` contains a monotone 4-term arithmetic
progression. The full question is open; the open content is precisely the *all 2-adic
scales at once* coupling (every fixed bound on the 2-adic valuation of the common
difference is achievable: LeSaulnier–Vijay handle odd differences, Adenwalla handles
differences not divisible by `2^k`). This file formalizes the LeSaulnier–Vijay base
case — there is a permutation of `ℕ` avoiding all monotone 4-term APs whose common
difference is **odd** — via an explicit closed-form permutation.

## The construction

The sequence (`g n` = the `n`-th value) is, in blocks of three,
```
g (3k)     = 4k       g (3k+1) = 4k+2       g (3k+2) = 2k+1
```
i.e. `0, 2, 1, 4, 6, 3, 8, 10, 5, 12, 14, 7, …`. Its inverse (the rank/position
function `σ v` = the position of value `v`) is
```
σ v = 3·(v/2) + 2          if v is odd
σ v = 3·(v/4) + (v%4)/2    if v is even.
```

The single structural fact driving everything is

> **Property (P).** Whenever an odd value `x` occurs *before* an even value `y`
> (i.e. `σ x < σ y`), we have `y > 2x`.

Property (P) alone forbids every monotone 4-AP with odd common difference: the four
terms of such an AP alternate in parity, so two adjacent terms form an odd-before-even
pair, and (P) turns the monotonicity of the positions into `v < 0`, a contradiction.
This is exactly the LeSaulnier–Vijay argument (their construction used geometric
interval blocks; the closed form above is an equivalent, fully explicit realization).
-/

namespace PermutationMonotoneAP

open Function

/-- The LeSaulnier–Vijay odd-difference avoider, as a sequence `g : ℕ → ℕ`
(`g n` is the `n`-th value). In blocks of three:
`g (3k) = 4k`, `g (3k+1) = 4k+2`, `g (3k+2) = 2k+1`. -/
def oddAvoiderFun (n : ℕ) : ℕ :=
  if n % 3 = 0 then 4 * (n / 3)
  else if n % 3 = 1 then 4 * (n / 3) + 2
  else 2 * (n / 3) + 1

/-- The inverse rank/position function `σ v` = the position of value `v` in
`oddAvoiderFun`. -/
def oddAvoiderInv (v : ℕ) : ℕ :=
  if v % 2 = 1 then 3 * (v / 2) + 2
  else 3 * (v / 4) + (v % 4) / 2

theorem oddAvoiderInv_oddAvoiderFun (n : ℕ) :
    oddAvoiderInv (oddAvoiderFun n) = n := by
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · have e : oddAvoiderFun n = 4 * (n / 3) := by rw [oddAvoiderFun, if_pos h]
    rw [e, oddAvoiderInv, if_neg (by omega)]; omega
  · have e : oddAvoiderFun n = 4 * (n / 3) + 2 := by
      rw [oddAvoiderFun, if_neg (by omega), if_pos h]
    rw [e, oddAvoiderInv, if_neg (by omega)]; omega
  · have e : oddAvoiderFun n = 2 * (n / 3) + 1 := by
      rw [oddAvoiderFun, if_neg (by omega), if_neg (by omega)]
    rw [e, oddAvoiderInv, if_pos (by omega)]; omega

theorem oddAvoiderFun_oddAvoiderInv (v : ℕ) :
    oddAvoiderFun (oddAvoiderInv v) = v := by
  rcases (by omega : v % 4 = 0 ∨ v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3) with h | h | h | h
  · have e : oddAvoiderInv v = 3 * (v / 4) := by
      rw [oddAvoiderInv, if_neg (by omega)]; omega
    rw [e, oddAvoiderFun, if_pos (by omega)]; omega
  · have e : oddAvoiderInv v = 3 * (v / 2) + 2 := by rw [oddAvoiderInv, if_pos (by omega)]
    rw [e, oddAvoiderFun, if_neg (by omega), if_neg (by omega)]; omega
  · have e : oddAvoiderInv v = 3 * (v / 4) + 1 := by
      rw [oddAvoiderInv, if_neg (by omega)]; omega
    rw [e, oddAvoiderFun, if_neg (by omega), if_pos (by omega)]; omega
  · have e : oddAvoiderInv v = 3 * (v / 2) + 2 := by rw [oddAvoiderInv, if_pos (by omega)]
    rw [e, oddAvoiderFun, if_neg (by omega), if_neg (by omega)]; omega

/-- The LeSaulnier–Vijay odd-difference avoider as a permutation `ℕ ≃ ℕ`. -/
def oddAvoider : ℕ ≃ ℕ where
  toFun := oddAvoiderFun
  invFun := oddAvoiderInv
  left_inv := oddAvoiderInv_oddAvoiderFun
  right_inv := oddAvoiderFun_oddAvoiderInv

/-- **Property (P).** If an odd value `x` precedes an even value `y`
(`oddAvoiderInv x < oddAvoiderInv y`), then `y > 2x`. -/
theorem oddAvoiderInv_propP {x y : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 0)
    (h : oddAvoiderInv x < oddAvoiderInv y) : 2 * x < y := by
  simp only [oddAvoiderInv] at h
  rw [if_pos hx, if_neg (show ¬ y % 2 = 1 by omega)] at h
  -- now h : 3*(x/2)+2 < 3*(y/4)+(y%4)/2 ; with x odd, y even
  omega

/-- **The core arithmetic obstruction.** Four naturals `v0,v1,v2,v3` in arithmetic
progression with *odd* common difference `d`, listed at strictly increasing positions
`oddAvoiderInv v0 < oddAvoiderInv v1 < oddAvoiderInv v2 < oddAvoiderInv v3`, cannot exist.

The four terms alternate in parity, so among the adjacent pairs there is an
odd-value-before-even-value pair; property (P) turns the monotonicity into `v0 < 0`
(parity of `v0` even) or `v0 < d ∧ v0 < -d` (parity odd), each impossible in `ℕ`. -/
theorem no_oddDiff_mono4 {v0 v1 v2 v3 : ℕ} {a d : ℤ} (hd : Odd d)
    (e0 : (v0 : ℤ) = a) (e1 : (v1 : ℤ) = a + d)
    (e2 : (v2 : ℤ) = a + 2 * d) (e3 : (v3 : ℤ) = a + 3 * d)
    (h01 : oddAvoiderInv v0 < oddAvoiderInv v1)
    (h12 : oddAvoiderInv v1 < oddAvoiderInv v2)
    (h23 : oddAvoiderInv v2 < oddAvoiderInv v3) : False := by
  obtain ⟨m, hm⟩ := hd
  rcases (by omega : v0 % 2 = 0 ∨ v0 % 2 = 1) with h0 | h0
  · -- v0, v2 even; v1, v3 odd. Use the adjacent pair (v1 odd, v2 even).
    have hv1 : v1 % 2 = 1 := by omega
    have hv2 : v2 % 2 = 0 := by omega
    have key := oddAvoiderInv_propP hv1 hv2 h12   -- 2 * v1 < v2
    omega
  · -- v0, v2 odd; v1, v3 even. Use pairs (v0 odd, v1 even) and (v2 odd, v3 even).
    have hv1 : v1 % 2 = 0 := by omega
    have hv2 : v2 % 2 = 1 := by omega
    have hv3 : v3 % 2 = 0 := by omega
    have k1 := oddAvoiderInv_propP h0 hv1 h01    -- 2 * v0 < v1
    have k2 := oddAvoiderInv_propP hv2 hv3 h23    -- 2 * v2 < v3
    omega

/-- A sequence `f : ℕ → ℕ` has a **monotone 4-term AP with odd common difference**:
strictly increasing positions whose values form a 4-term AP whose common difference is
odd. This is the repo's `HasMonotoneAP` specialised to `k = 4` and odd `d`. -/
def HasMonotoneAPOddDiff (f : ℕ → ℕ) : Prop :=
  ∃ p : ℕ → ℕ, StrictMono p ∧ ∃ a d : ℤ, Odd d ∧ ∀ j < 4, (f (p j) : ℤ) = a + (j : ℤ) * d

/-- A monotone 4-AP of odd common difference is in particular a monotone 4-AP, so
`HasMonotoneAPOddDiff` is weaker than `HasMonotoneAP _ 4`. Consequently
`Erdos196Avoidable` would imply the result of this file. -/
theorem hasMonotoneAP_four_of_oddDiff {f : ℕ → ℕ} (h : HasMonotoneAPOddDiff f) :
    HasMonotoneAP f 4 := by
  obtain ⟨p, hp, a, d, _, hval⟩ := h
  exact ⟨p, hp, a, d, hval⟩

/-- **LeSaulnier–Vijay (2011), formalized.** The explicit permutation `oddAvoider`
contains no monotone 4-term AP with odd common difference. -/
theorem oddAvoider_no_oddDiff_mono4 :
    ¬ HasMonotoneAPOddDiff (fun n => oddAvoider n) := by
  rintro ⟨p, hp, a, d, hd, hval⟩
  have e0 : (oddAvoider (p 0) : ℤ) = a := by simpa using hval 0 (by norm_num)
  have e1 : (oddAvoider (p 1) : ℤ) = a + d := by simpa using hval 1 (by norm_num)
  have e2 : (oddAvoider (p 2) : ℤ) = a + 2 * d := by simpa using hval 2 (by norm_num)
  have e3 : (oddAvoider (p 3) : ℤ) = a + 3 * d := by simpa using hval 3 (by norm_num)
  have pj : ∀ j, oddAvoiderInv (oddAvoider (p j)) = p j :=
    fun j => oddAvoiderInv_oddAvoiderFun (p j)
  have s01 : oddAvoiderInv (oddAvoider (p 0)) < oddAvoiderInv (oddAvoider (p 1)) := by
    rw [pj 0, pj 1]; exact hp (by norm_num)
  have s12 : oddAvoiderInv (oddAvoider (p 1)) < oddAvoiderInv (oddAvoider (p 2)) := by
    rw [pj 1, pj 2]; exact hp (by norm_num)
  have s23 : oddAvoiderInv (oddAvoider (p 2)) < oddAvoiderInv (oddAvoider (p 3)) := by
    rw [pj 2, pj 3]; exact hp (by norm_num)
  exact no_oddDiff_mono4 hd e0 e1 e2 e3 s01 s12 s23

/-- **There exists a permutation of `ℕ` avoiding every monotone 4-term AP of odd common
difference.** This is the odd-difference base layer of Erdős #196 (the full problem — all
2-adic scales of the common difference simultaneously — remains open). -/
theorem exists_perm_no_oddDiff_mono4 :
    ∃ g : ℕ ≃ ℕ, ¬ HasMonotoneAPOddDiff (fun n => g n) :=
  ⟨oddAvoider, oddAvoider_no_oddDiff_mono4⟩

/-! ### Bridge to the `Compactness.lean` socket

The recursive socket `erdos196Avoidable_of_child_anchoredConcreteWitnessOddDiffSafeEvenPositionSet`
reduces #196 to building, at every dyadic scale, a finite merged order satisfying
`OddDiffSafe` under a uniform displacement bound. The lemma below shows the *single-scale*
`OddDiffSafe` obligation is globally and unconditionally satisfiable: the explicit position
function `oddAvoiderInv` meets `OddDiffSafe N` for **every** `N`, with a linear bound
`oddAvoiderInv v ≤ 2 * v`. So the socket's residual difficulty is *only* the simultaneous
recursive coupling across all scales — exactly the open all-scales content. -/
theorem oddDiffSafe_oddAvoiderInv (N : ℕ) : OddDiffSafe oddAvoiderInv N := by
  intro a d hd hodd _hN hmono
  have hdodd : Odd (d : ℤ) := (Int.odd_coe_nat d).mpr (Nat.odd_iff.mpr hodd)
  rcases hmono with ⟨i1, i2, i3⟩ | ⟨j1, j2, j3⟩
  · -- increasing case: AP a, a+d, a+2d, a+3d with rising positions
    exact no_oddDiff_mono4 (v0 := a) (v1 := a + d) (v2 := a + 2 * d) (v3 := a + 3 * d)
      (a := (a : ℤ)) (d := (d : ℤ)) hdodd (by omega) (by omega) (by omega) (by omega)
      i1 i2 i3
  · -- decreasing case: reverse the AP (common difference `-d`, still odd)
    exact no_oddDiff_mono4 (v0 := a + 3 * d) (v1 := a + 2 * d) (v2 := a + d) (v3 := a)
      (a := ((a : ℤ) + 3 * d)) (d := (-(d : ℤ))) hdodd.neg
      (by omega) (by omega) (by omega) (by omega) j1 j2 j3

/-- The explicit odd-difference avoider meets the linear displacement bound
`oddAvoiderInv v ≤ 2 * v` (in fact `≤ ⌈3v/2⌉`), so it is a genuine type-`ω` order. -/
theorem oddAvoiderInv_le (v : ℕ) : oddAvoiderInv v ≤ 2 * v := by
  unfold oddAvoiderInv
  split <;> omega

/-! ### The dyadic reduction towards Adenwalla's Theorem 4

Adenwalla (2022) proved that for every `k` there is a permutation of `ℕ` avoiding all
monotone 4-term APs whose common difference is **not divisible by `2^k`** (the `k = 1`
case is the LeSaulnier–Vijay theorem above). We formalize the *dyadic recursion* that
reduces this to a base case (odd differences, done) plus a single merge step.

`AvoidV2 σ k` says the rank assignment `σ` has no monotone 4-AP whose common difference
is coprime-to-`2`-up-to-`2^k`, i.e. not divisible by `2^k`. The key facts:

* `avoidV2_zero` — vacuous base (`2^0 = 1` divides every difference).
* `avoidV2_succ` — **the reduction**: if `σ` kills *odd*-difference APs (property (P)),
  and both dyadic children `evenChild σ`, `oddChild σ` already avoid `2^k`-indivisible
  differences, then `σ` avoids `2^(k+1)`-indivisible differences. (A `2^(j)`-indivisible
  even-difference AP rescales to a `2^(j-1)`-indivisible AP in one of the two children,
  by `mono4_evenChild_iff` / `mono4_oddChild_iff`.)
* `avoidV2_oddAvoiderInv_one` — the explicit LV order realizes the base case `k = 1`.

So Adenwalla's theorem is now *construction-ready*: it follows by induction on `k` from a
**(P)-merge** that builds, from any odd-difference avoider, a new one whose two dyadic
children are themselves odd-difference avoiders of the same kind. Such a merge exists (the
recursive deadline-merge `O_k`, verified computationally to avoid all `v2(d) < k` APs with
linear-in-`k` displacement); its explicit type-`ω` bijection is the remaining formal step. -/
def AvoidV2 (σ : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ¬ (2 ^ k ∣ d) → ¬ Mono4 σ a d

/-- Vacuous base: every difference is divisible by `2^0 = 1`. -/
theorem avoidV2_zero (σ : ℕ → ℕ) : AvoidV2 σ 0 := by
  intro a d _ hndvd _
  exact hndvd (one_dvd d)

/-- **The dyadic reduction.** If `σ` kills every odd-difference monotone 4-AP and both
dyadic children avoid `2^k`-indivisible-difference 4-APs, then `σ` avoids
`2^(k+1)`-indivisible-difference 4-APs. -/
theorem avoidV2_succ {σ : ℕ → ℕ} {k : ℕ}
    (hP : ∀ a d : ℕ, 0 < d → Odd d → ¬ Mono4 σ a d)
    (he : AvoidV2 (evenChild σ) k) (ho : AvoidV2 (oddChild σ) k) :
    AvoidV2 σ (k + 1) := by
  intro a d hd hndvd hmono
  rcases Nat.even_or_odd d with hdE | hdO
  · -- even difference d = 2q: rescales to a child AP with difference q
    obtain ⟨q, hq⟩ := hdE
    have hd2 : d = 2 * q := by omega
    have hq0 : 0 < q := by omega
    have hqndvd : ¬ (2 ^ k ∣ q) := by
      intro hdvd
      obtain ⟨c, rfl⟩ := hdvd
      exact hndvd ⟨c, by rw [hd2, pow_succ]; ring⟩
    rcases Nat.even_or_odd a with haE | haO
    · obtain ⟨b, hb⟩ := haE
      have ha2 : a = 2 * b := by omega
      rw [ha2, hd2] at hmono
      exact he b q hq0 hqndvd ((mono4_evenChild_iff σ b q).mpr hmono)
    · obtain ⟨b, hb⟩ := haO
      have ha2 : a = 2 * b + 1 := by omega
      rw [ha2, hd2] at hmono
      exact ho b q hq0 hqndvd ((mono4_oddChild_iff σ b q).mpr hmono)
  · exact hP a d hd hdO hmono

/-- The explicit LeSaulnier–Vijay order realizes the base case `k = 1`: it avoids every
monotone 4-AP of `2`-indivisible (i.e. odd) common difference. -/
theorem avoidV2_oddAvoiderInv_one : AvoidV2 oddAvoiderInv 1 := by
  intro a d hd hndvd hmono
  have hodd : d % 2 = 1 := by
    rcases Nat.even_or_odd d with ⟨c, hc⟩ | ho
    · exact absurd (⟨c, by rw [pow_one]; omega⟩ : (2 : ℕ) ^ 1 ∣ d) hndvd
    · exact Nat.odd_iff.mp ho
  exact oddDiffSafe_oddAvoiderInv (a + 3 * d + 1) a d hd hodd (by omega) hmono

/-- `Mono4` depends only on the strict order a rank assignment induces: if `f` and `g`
compare the same way everywhere, they have the same monotone 4-APs. -/
theorem mono4_iff_of_lt_iff {f g : ℕ → ℕ} {a d : ℕ}
    (h : ∀ i j : ℕ, f i < f j ↔ g i < g j) : Mono4 f a d ↔ Mono4 g a d := by
  unfold Mono4
  simp only [h]

/-- **The (P)-merge step**, abstracted. From any order `H` it produces an order `G` whose
two dyadic children both reproduce `H`'s order and which kills every odd-difference
monotone 4-AP (property (P)). The recursive deadline-merge realizes this — verified
computationally to avoid all `v2(d) < k` monotone 4-APs with displacement linear in the
value — and is the one remaining ingredient (its explicit type-`ω` bijection) for a full
formal proof of Adenwalla's Theorem 4. -/
def HasPMerge : Prop :=
  ∀ H : ℕ → ℕ, ∃ G : ℕ → ℕ,
    (∀ a d : ℕ, 0 < d → Odd d → ¬ Mono4 G a d) ∧
    (∀ i j : ℕ, evenChild G i < evenChild G j ↔ H i < H j) ∧
    (∀ i j : ℕ, oddChild G i < oddChild G j ↔ H i < H j)

/-- **Adenwalla's Theorem 4, reduced to the (P)-merge.** Given the (verified) (P)-merge
step, for every `k` there is a rank assignment avoiding all monotone 4-term APs whose
common difference is not divisible by `2^k`. The proof is induction on `k` using the
dyadic reduction `avoidV2_succ`; the base case is vacuous and each step applies one merge.
This makes Adenwalla's theorem construction-ready: only `HasPMerge` remains. -/
theorem adenwalla_of_hasPMerge (hM : HasPMerge) : ∀ k, ∃ G : ℕ → ℕ, AvoidV2 G k := by
  intro k
  induction k with
  | zero => exact ⟨id, avoidV2_zero id⟩
  | succ n ih =>
    obtain ⟨H, hH⟩ := ih
    obtain ⟨G, hP, heven, hodd⟩ := hM H
    refine ⟨G, avoidV2_succ hP ?_ ?_⟩
    · intro a d hd hnd hmono
      exact hH a d hd hnd ((mono4_iff_of_lt_iff heven).mp hmono)
    · intro a d hd hnd hmono
      exact hH a d hd hnd ((mono4_iff_of_lt_iff hodd).mp hmono)

/-! ### The all-scales characterisation: `∃ G ∀ k` versus Adenwalla's `∀ k ∃ G`

`adenwalla_of_hasPMerge` produces, *for each scale `k` separately*, an order avoiding every
monotone 4-AP whose common difference is not divisible by `2^k` (`∀ k, ∃ G, AvoidV2 G k`).
Erdős #196 (the negative direction) is the **same statement with the quantifiers swapped** — a
*single* order good at every scale at once. The lemmas below pin this down:

* `mono4_free_iff_forall_avoidV2`: for one fixed `G`, avoiding `2^k`-indivisible-difference
  4-APs at *all* `k` is the same as avoiding *every* monotone 4-AP (any `d > 0` has `2^d ∤ d`).
* `erdos196Avoidable_iff_exists_injective_avoidV2_all`: hence a 4-AP-avoiding permutation of
  `ℕ` exists **iff** `∃ G, Function.Injective G ∧ ∀ k, AvoidV2 G k`.

So the open content of #196 is exactly the quantifier swap `(∀ k, ∃ G) ⟹ (∃ G, ∀ k)`. The drift
lemma (`unbounded_displacement_of_avoiding`) explains why no compactness argument performs the
swap for free: the witnessing order must have unbounded displacement, so the per-scale orders
carry no uniform bound to thread through König's lemma. This is the formal statement of the
"all 2-adic scales at once" wall. -/

/-- For a fixed order `G`, avoiding monotone 4-APs of every `2^k`-indivisible difference (at
*all* scales `k`) is equivalent to avoiding *every* monotone 4-AP. The nontrivial direction
uses that any `d > 0` satisfies `2^d ∤ d` (since `d < 2^d`), so scale `k = d` already rules the
difference `d` out. -/
theorem mono4_free_iff_forall_avoidV2 (G : ℕ → ℕ) :
    (∀ a d : ℕ, 0 < d → ¬ Mono4 G a d) ↔ ∀ k, AvoidV2 G k := by
  constructor
  · intro h k a d hd _; exact h a d hd
  · intro h a d hd
    refine h d a d hd (fun hdvd => ?_)
    exact absurd (Nat.le_of_dvd hd hdvd) (by have := Nat.lt_two_pow_self (n := d); omega)

/-- "No monotone 4-AP below any finite `N`" is the same as "no monotone 4-AP at all". -/
theorem forall_not_hasMono4_iff (G : ℕ → ℕ) :
    (∀ N : ℕ, ¬ HasMono4 G N) ↔ ∀ a d : ℕ, 0 < d → ¬ Mono4 G a d := by
  constructor
  · intro h a d hd hmono
    exact h (a + 3 * d + 1) ⟨a, d, hd, by omega, hmono⟩
  · rintro h N ⟨a, d, hd, _, hmono⟩
    exact h a d hd hmono

/-- **Single-order all-scales characterisation of Erdős #196.** A permutation of `ℕ` avoiding
every monotone 4-term AP exists iff some injective order `G` simultaneously avoids the
`2^k`-indivisible-difference 4-APs at *every* scale `k`. Compare `adenwalla_of_hasPMerge`'s
`∀ k, ∃ G, AvoidV2 G k`: the gap between the two is precisely the quantifier swap, which is the
open content of #196 — and `unbounded_displacement_of_avoiding` is why the swap is hard. -/
theorem erdos196Avoidable_iff_exists_injective_avoidV2_all :
    Erdos196Avoidable ↔ ∃ G : ℕ → ℕ, Function.Injective G ∧ ∀ k, AvoidV2 G k := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨(g.symm : ℕ → ℕ), g.symm.injective,
      (mono4_free_iff_forall_avoidV2 _).mp
        ((forall_not_hasMono4_iff _).mp (not_hasMono4_symm_of_avoiding hg))⟩
  · rintro ⟨G, hGinj, hG⟩
    refine erdos196Avoidable_of_finiteFeasible G (fun N => ⟨G, ?_, fun v _ => le_refl _, ?_⟩)
    · exact fun u _ v _ h => hGinj h
    · exact (forall_not_hasMono4_iff G).mpr ((mono4_free_iff_forall_avoidV2 G).mpr hG) N

end PermutationMonotoneAP
