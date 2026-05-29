import Erdos.PermutationMonotoneAP.Statement
import Erdos.PermutationMonotoneAP.Density

/-!
# The reflection leak at records (Attack C on Erdős #197)

Fix a 3-free enumeration `e : ℕ ≃ S` of a set `S ⊆ ℕ`. Write `Pₜ = {e 0, …, e (t-1)}`
for the set of values placed strictly before time `t`.

**The symmetric-placement rule.** `e` avoids monotone 3-APs iff for every `t` and
every `d ≥ 1` with both `e t - d ∈ S` and `e t + d ∈ S`, the two reflections lie on
the *same temporal side* of `e t`: `(e t - d ∈ Pₜ) ↔ (e t + d ∈ Pₜ)`. (A monotone
3-AP is exactly a value-midpoint `e t` placed temporally between its two endpoints.)

**The reflection leak (this file).** When `M := e t` is a *record* — a left-to-right
maximum of the value sequence, `e s < M` for all `s < t` — every earlier value `p ∈ Pₜ`
satisfies `p < M`, so its reflection `2M - p` lies strictly to the right of `M`, beyond
everything placed so far. The rule then forces `2M - p ∉ S`. Hence

> `s ↦ 2M - e s` injects `Pₜ` into `Sᶜ ∩ (M, 2M]`, so `t ≤ |Sᶜ ∩ (M, 2M]|`.

This is the precise quantitative mechanism behind the conjectural value `α(3) = 1/2`
(it is the `z ≥ 2y` inequality of the LeSaulnier–Vijay construction): every record
forces a proportional amount of complement immediately to its right.

**Main results.**
* `reflection_avoids_of_record` — the pointwise leak: each `2M - e s ∉ S`.
* `reflection_leak` — the counting form `t ≤ ncard (Sᶜ ∩ Ioc M (2M))`.
* `lowerDensity_le_of_records_dense` — *conditional* density bound: if the records have
  positive lower density `c` on the value scale (rank `≥ c · value` infinitely often),
  then `upperDensity Sᶜ ≥ c / 2`, so `lowerDensity S ≤ 1 - c/2 < 1`. A genuine sufficient
  condition for `β(3) < 1` (Erdős #197).
* `recordValues_no_threeAP` — the set of record *values* is itself **3-AP-free**. (So by
  Roth's theorem the *number of distinct record values* below `M` is `o(M)`. Crucially this
  bounds the record **index**, not the record **rank** `t` that powers the leak — the two
  are decoupled, so this does **not** make the leak `o(N)`.)

**Status (honest).** `lowerDensity_le_of_records_dense` **reduces** the open problem
`β(3) < 1` to a clean **order-type** statement: *is there a uniform `c > 0` such that every
3-free enumeration has records of rank `t ≥ c · value` arbitrarily late?* The hypothesis is
**not** vacuous — the LeSaulnier–Vijay set satisfies it with `c ≈ 1/6` (its records occur at
rank proportional to their value, consistent with its true lower density `1/4`). What remains
open is whether an adversary could instead build a density-`→1` 3-free set whose late records
all have rank `o(value)` (a "sparse rightward skeleton"); ruling that out is exactly the
order-type/Ramsey content that the counting leak does not by itself supply.

Reference: LeSaulnier, Vijay, *On permutations avoiding arithmetic progressions*,
arXiv:1004.1740.
-/

namespace PermutationMonotoneAP

open Filter

variable {S : Set ℕ}

/-- **Record (left-to-right maximum).** Position `t` carries a record value in the
enumeration `e` if every earlier position carries a strictly smaller value. -/
def IsRecord (e : ℕ ≃ S) (t : ℕ) : Prop := ∀ s, s < t → ((e s : ℕ)) < (e t : ℕ)

/-- **Pointwise reflection leak.** Let `e` avoid monotone 3-APs and let `M = e t` be a
record. Then for every earlier position `s < t`, the reflected point `2M - e s` is *not*
in `S`.

Proof: write `p = e s < M`, so `R := 2M - p` satisfies `p < M < R` and `p + R = 2M`,
i.e. `(p, M, R)` is a 3-term AP with value-midpoint `M`. If `R ∈ S`, say at position
`u = e.symm R`, then `R > M ≥ e w` for all `w ≤ t` (as `M` is a record), so `R` occurs
strictly after position `t`; thus `s < t < u` are increasing positions whose values
`p, M, R` form an AP — a monotone 3-AP, contradiction. -/
theorem reflection_avoids_of_record (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3) {t : ℕ} (hrec : IsRecord e t)
    {s : ℕ} (hs : s < t) : (2 * (e t : ℕ) - (e s : ℕ)) ∉ S := by
  intro hR
  set M := (e t : ℕ) with hM
  set p := (e s : ℕ) with hp
  have hpM : p < M := hrec s hs
  set R := 2 * M - p with hRdef
  -- position of R in the enumeration
  set u := e.symm ⟨R, hR⟩ with hu
  have hval_u : (e u : ℕ) = R := by rw [hu]; simp
  -- M is the running maximum up to time t: every value at position ≤ t is ≤ M
  have hle_t : ∀ w, w ≤ t → (e w : ℕ) ≤ M := by
    intro w hw
    rcases lt_or_eq_of_le hw with hlt | heq
    · exact (hrec w hlt).le
    · rw [heq]
  -- R is a new value, strictly above M, so it appears after position t
  have hRM : M < R := by rw [hRdef]; omega
  have ht_lt_u : t < u := by
    by_contra hle
    rw [not_lt] at hle
    have := hle_t u hle
    rw [hval_u] at this
    omega
  -- assemble the monotone 3-AP at increasing positions s < t < u
  apply he
  refine ⟨fun j => match j with | 0 => s | 1 => t | (n + 2) => u + n, ?_,
          (p : ℤ), (M : ℤ) - (p : ℤ), ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact hs
    | 1 => exact ht_lt_u
    | (n + 2) => simp only; omega
  · intro j hj
    have hRcast : (R : ℤ) = 2 * (M : ℤ) - (p : ℤ) := by
      rw [hRdef, Nat.cast_sub (by omega : p ≤ 2 * M)]; push_cast; ring
    interval_cases j
    · simp [hp]
    · simp only; rw [hM]; push_cast; ring
    · simp only [Nat.add_zero, hval_u, hRcast]; push_cast; ring

/-- **The reflection leak (counting form).** If `e` avoids monotone 3-APs and `M = e t`
is a record, then `t ≤ |Sᶜ ∩ (M, 2M]|`: the `t` reflections `2M - e s` (`s < t`) are
distinct points of the complement of `S` lying in the half-open interval `(M, 2M]`.

This is the quantitative core of Attack C: a record at time `t` forces at least `t`
missing points immediately to its right, in an interval of length `M`. -/
theorem reflection_leak (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3) {t : ℕ} (hrec : IsRecord e t) :
    t ≤ (Sᶜ ∩ Set.Ioc (e t : ℕ) (2 * (e t : ℕ))).ncard := by
  set M := (e t : ℕ) with hM
  -- the reflection map and its image of the positions `< t`
  set F : ℕ → ℕ := fun s => 2 * M - (e s : ℕ) with hF
  set J := F '' Set.Iio t with hJ
  -- `F` is injective on `Iio t` (`e` injective and all values `< M = e t ≤ 2M`)
  have hinjOn : Set.InjOn F (Set.Iio t) := by
    intro a ha b hb hab
    simp only [hF] at hab
    have hpa : (e a : ℕ) < M := hrec a ha
    have hpb : (e b : ℕ) < M := hrec b hb
    have hva : (e a : ℕ) = (e b : ℕ) := by omega
    exact e.injective (Subtype.ext hva)
  -- the image lands in `Sᶜ ∩ (M, 2M]`
  have hsub : J ⊆ Sᶜ ∩ Set.Ioc M (2 * M) := by
    rintro _ ⟨s, hs, rfl⟩
    have hsM : (e s : ℕ) < M := hrec s hs
    refine ⟨reflection_avoids_of_record e he hrec hs, ?_, ?_⟩
    · simp only [hF]; omega
    · simp only [hF]; omega
  -- both sets are finite (subsets of the finite interval `(M, 2M]`)
  have hfin : (Sᶜ ∩ Set.Ioc M (2 * M)).Finite :=
    (Set.finite_Ioc M (2 * M)).subset Set.inter_subset_right
  -- count: `|J| = |Iio t| = t`, and `J ⊆ target`
  have hcardJ : J.ncard = t := by
    rw [hJ, hinjOn.ncard_image, Set.ncard_Iio_nat]
  calc t = J.ncard := hcardJ.symm
    _ ≤ (Sᶜ ∩ Set.Ioc M (2 * M)).ncard := Set.ncard_le_ncard hsub hfin

/-- **The reflection leak (counting-function form).** For a record `M = e t`, the rank
`t` is at most the number of complement elements below `2M + 1`:
`t ≤ countMem Sᶜ (2 (e t) + 1)`. (Repackages `reflection_leak` through the prefix
counting function `countMem`, since `(M, 2M] ⊆ [0, 2M + 1)`.) -/
theorem record_rank_le_countMem_compl (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3) {t : ℕ} (hrec : IsRecord e t) :
    t ≤ countMem Sᶜ (2 * (e t : ℕ) + 1) := by
  refine (reflection_leak e he hrec).trans ?_
  apply Set.ncard_le_ncard _ ((Set.finite_Iio _).subset Set.inter_subset_right)
  rintro x ⟨hxc, hx1, hx2⟩
  exact ⟨hxc, by simp only [Set.mem_Iio]; omega⟩

/-- **Position `0` is always a record.** -/
theorem isRecord_zero (e : ℕ ≃ S) : IsRecord e 0 := fun s hs => absurd hs (Nat.not_lt_zero s)

/-- **A record's value is at least its rank**: if `e t` is a record, then `t ≤ e t`.
(The `t` distinct earlier values `e 0, …, e (t-1)` are all `< e t`, so they are `t`
distinct elements of `{0, …, e t - 1}`.) -/
theorem rank_le_record_value (e : ℕ ≃ S) {t : ℕ} (hrec : IsRecord e t) : t ≤ (e t : ℕ) := by
  -- `e '' Iio t ⊆ Iio (e t)` and `e` is injective, so `t = |Iio t| ≤ |Iio (e t)| = e t`
  have hsub : (fun s => (e s : ℕ)) '' Set.Iio t ⊆ Set.Iio (e t : ℕ) := by
    rintro _ ⟨s, hs, rfl⟩; exact hrec s hs
  have hinj : Set.InjOn (fun s => (e s : ℕ)) (Set.Iio t) := by
    intro a _ b _ hab; exact e.injective (Subtype.ext hab)
  have := Set.ncard_le_ncard hsub (Set.finite_Iio _)
  rwa [hinj.ncard_image, Set.ncard_Iio_nat, Set.ncard_Iio_nat] at this

/-- **Records are linearly ordered by value and rank together.** If positions `s` and `u`
both carry records and `e s < e u`, then `s < u` (a smaller record-value occurs earlier).

This is the key fact behind "the record values are 3-AP-free": records, listed in value
order, are also in rank (temporal) order. -/
theorem record_lt_of_value_lt (e : ℕ ≃ S) {s u : ℕ} (hrs : IsRecord e s) (_hru : IsRecord e u)
    (hlt : (e s : ℕ) < (e u : ℕ)) : s < u := by
  rcases lt_trichotomy s u with h | h | h
  · exact h
  · subst h; exact absurd hlt (lt_irrefl _)
  · -- `u < s` and `e s` a record ⟹ `e u < e s`, contradicting `e s < e u`
    exact absurd (hrs u h) (by omega)

/-- **The record values form a 3-AP-free set.** For any enumeration `e` avoiding monotone
3-APs, there is no 3-term arithmetic progression `x, x+d, x+2d` (`d ≥ 1`) all of whose
terms are record values.

Proof: records, listed in increasing value, occur at increasing ranks
(`record_lt_of_value_lt`). So if `x < x+d < x+2d` are all records, their ranks are
increasing — and the values form an AP — giving a monotone 3-AP, contradiction.

**Consequence (via Roth's theorem — not formalized here).** A 3-AP-free subset of `[0, M]`
has size `o(M)`, so the *number of distinct record values* below `M` is `o(M)`. This bounds
the record **index**; it does **not** bound the record **rank** `t` (the quantity in
`reflection_leak`), which is a different, decoupled count. So it does *not* by itself weaken
the leak — indeed the LeSaulnier–Vijay set has record ranks `t ≍ value`. -/
theorem recordValues_no_threeAP (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3) (x d : ℕ) (hd : 0 < d)
    (hx : ∃ t, IsRecord e t ∧ (e t : ℕ) = x)
    (hy : ∃ t, IsRecord e t ∧ (e t : ℕ) = x + d)
    (hz : ∃ t, IsRecord e t ∧ (e t : ℕ) = x + 2 * d) : False := by
  obtain ⟨sx, hrx, hvx⟩ := hx
  obtain ⟨sy, hry, hvy⟩ := hy
  obtain ⟨sz, hrz, hvz⟩ := hz
  -- ranks are strictly increasing since values are
  have hxy : sx < sy := record_lt_of_value_lt e hrx hry (by omega)
  have hyz : sy < sz := record_lt_of_value_lt e hry hrz (by omega)
  -- assemble the monotone 3-AP at positions sx < sy < sz
  apply he
  refine ⟨fun j => match j with | 0 => sx | 1 => sy | (n + 2) => sz + n, ?_,
          (x : ℤ), (d : ℤ), ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact hxy
    | 1 => exact hyz
    | (n + 2) => simp only; omega
  · intro j hj
    interval_cases j
    · simp [hvx]
    · simp only; rw [hvy]; push_cast; ring
    · simp only [Nat.add_zero]; rw [hvz]; push_cast; ring

/-- **Records have arbitrarily large value.** For every bound `V`, some record `e t`
exceeds `V`. (Take `t` to be a position achieving the maximum value over `{0, …, n}`
for `n` large enough that some value beyond `V` has appeared; an argmax over an initial
segment is automatically a record.) -/
theorem exists_record_value_gt (e : ℕ ≃ S) (V : ℕ) :
    ∃ t, IsRecord e t ∧ V < (e t : ℕ) := by
  classical
  -- a position with value `> V` exists, since the values are unbounded (`e` injective into `ℕ`)
  obtain ⟨n, hn⟩ : ∃ n, V < (e n : ℕ) := by
    by_contra h
    rw [not_exists] at h
    simp only [not_lt] at h
    -- then `e` maps `ℕ` into the finite set `Iic V`, contradicting injectivity
    have : Function.Injective (fun k => (e k : ℕ)) := fun a b hab => e.injective (Subtype.ext hab)
    have hrange : (Set.range (fun k => (e k : ℕ))).Infinite :=
      Set.infinite_range_of_injective this
    have hbdd : Set.range (fun k => (e k : ℕ)) ⊆ Set.Iic V := by
      rintro _ ⟨k, rfl⟩; exact h k
    exact hrange ((Set.finite_Iic V).subset hbdd)
  -- argmax of values over `{0, …, n}`
  obtain ⟨t, htle, htmax⟩ : ∃ t ∈ Finset.range (n + 1),
      ∀ s ∈ Finset.range (n + 1), (e s : ℕ) ≤ (e t : ℕ) :=
    Finset.exists_max_image (Finset.range (n + 1)) (fun s => (e s : ℕ)) ⟨n, by simp⟩
  have htn : t ≤ n := by simpa [Nat.lt_succ_iff] using htle
  refine ⟨t, ?_, ?_⟩
  · -- `t` is a record: any `s < t` has `s ≤ n`, so `e s ≤ e t`, and `e s ≠ e t`
    intro s hs
    have hsn : s ∈ Finset.range (n + 1) := by simp; omega
    have hle := htmax s hsn
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (e.injective (Subtype.ext h)) (by omega)
  · -- value at `t` is ≥ value at `n` > V
    have hnle := htmax n (by simp)
    omega

/-!
## Conditional density bound (a reduction of `β(3) < 1`)

The reflection leak says a record at rank `t` with value `M` forces `t` complement points
in `(M, 2M]`. If the records are *dense on the value scale* — quantitatively, if infinitely
many records have rank `t ≥ c · M` for some `c > 0` — then along the subsequence `n = 2M+1`
the complement density ratio is at least `c · M / (2M + 1) → c/2`. Hence
`upperDensity Sᶜ ≥ c/2`, so `S` cannot have lower density `1`
(`lowerDensity_le_of_records_dense`).

This **reduces** `β(3) < 1` to a single order-type lemma: prove the hypothesis holds with a
**uniform** `c > 0` over *every* 3-free enumeration (equivalently, that `limsup` over records
of `rank / value` is bounded below by a universal constant). The hypothesis is **non-vacuous**:
the LeSaulnier–Vijay extremizer satisfies it with `c ≈ 1/6` (its record rank is proportional
to its value), so the bound is genuinely applicable, not empty — it correctly yields
`lowerDensity ≤ 1 - c/2`, consistent with the true value `1/4`. **The open content** is
whether an adversary can defeat it: build a density-`→1` 3-free set whose late records all
have rank `o(value)` (a sparse rightward skeleton). Whether such a skeleton can coexist with
the *interior* placements needed to reach high density is an order-type/Ramsey question the
reflection count does not settle — the same `ω`-vs-finite gap as DEGS, localized to the
record-rank profile.
-/

/-- The complement density ratio at `n = 2M + 1` for a record of value `M` and rank `t`
with `c · M ≤ t` is at least `c · M / (2M + 1)`. -/
theorem densityRatio_compl_ge_at_record (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3) {t : ℕ} (hrec : IsRecord e t) {c : ℝ}
    (hct : c * (e t : ℕ) ≤ t) :
    c * (e t : ℕ) / (2 * (e t : ℕ) + 1) ≤ densityRatio Sᶜ (2 * (e t : ℕ) + 1) := by
  have hleak : (t : ℝ) ≤ (countMem Sᶜ (2 * (e t : ℕ) + 1) : ℝ) := by
    exact_mod_cast record_rank_le_countMem_compl e he hrec
  have hpos : (0 : ℝ) < 2 * (e t : ℕ) + 1 := by positivity
  have hcast : ((2 * (e t : ℕ) + 1 : ℕ) : ℝ) = 2 * (e t : ℕ) + 1 := by push_cast; ring
  rw [densityRatio, hcast]
  gcongr
  -- `c · M ≤ t ≤ countMem Sᶜ (2M+1)`
  calc c * (e t : ℕ) ≤ (t : ℝ) := hct
    _ ≤ (countMem Sᶜ (2 * (e t : ℕ) + 1) : ℝ) := hleak

/-- Arithmetic fact: for `c > 0`, `y < c/2`, and `E` a large enough natural number, the
ratio `c·E/(2E+1)` exceeds `y`. (Used to take the limit `c·E/(2E+1) → c/2` from below.) -/
theorem ratio_ge_of_large {c y : ℝ} (hy2 : y < c / 2) {E : ℕ}
    (hE : y / (c - 2 * y) ≤ E) (hEpos : 0 < E) : y ≤ c * E / (2 * E + 1) := by
  have hc2y : 0 < c - 2 * y := by linarith
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hden : (0 : ℝ) < 2 * E + 1 := by positivity
  rw [le_div_iff₀ hden]
  -- `y(2E+1) ≤ cE  ⟺  E(c - 2y) ≥ y`, and `E ≥ y/(c-2y)` gives exactly that
  have : y ≤ E * (c - 2 * y) := by
    rw [div_le_iff₀ hc2y] at hE; linarith
  nlinarith [this]

/-- **Conditional density bound (toward `β(3) < 1`).** Let `e` be an enumeration of `S`
avoiding monotone 3-APs. If for some `c > 0` there are arbitrarily late records whose rank
`t` is at least `c · (e t)` (records "dense on the value scale"), then the complement of
`S` has upper density at least `c / 2`.

This is the precise quantitative payoff of the reflection leak: the records pump a positive
density of complement to their right whenever they are not too sparse. -/
theorem upperDensity_compl_ge_of_records_dense {c : ℝ} (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3)
    (hrec : ∀ N, ∃ t, N ≤ t ∧ IsRecord e t ∧ c * (e t : ℕ) ≤ t) :
    c / 2 ≤ upperDensity Sᶜ := by
  rw [upperDensity, Filter.le_limsup_iff' (isCoboundedUnder_le_densityRatio Sᶜ)
      (isBoundedUnder_le_densityRatio Sᶜ)]
  -- it suffices that for every `y < c/2`, the complement density ratio is `≥ y` infinitely often
  intro y hy
  rw [Filter.frequently_atTop]
  intro M
  -- choose a record `t` so late that its value `E := e t` makes `c·E/(2E+1) ≥ y` and `2E+1 ≥ M`
  have hc2y : 0 < c - 2 * y := by linarith
  -- pick a natural `N` past both thresholds (`E ≥ t ≥ N` for a record)
  set Nthr : ℕ := max (⌈y / (c - 2 * y)⌉₊ + 1) (M + 1) with hNthr
  obtain ⟨t, htN, hrecord, hct⟩ := hrec Nthr
  set E := (e t : ℕ) with hE
  have hEt : t ≤ E := rank_le_record_value e hrecord
  have hEN : Nthr ≤ E := le_trans htN hEt
  have hEpos : 0 < E := lt_of_lt_of_le (by positivity) (le_trans (Nat.le_max_left _ _) hEN)
  -- the position `n = 2E + 1` works
  refine ⟨2 * E + 1, ?_, ?_⟩
  · -- `2E + 1 ≥ M`
    have : M + 1 ≤ E := le_trans (Nat.le_max_right _ _) hEN
    omega
  · -- density ratio at `2E+1` is `≥ c·E/(2E+1) ≥ y`
    refine le_trans ?_ (densityRatio_compl_ge_at_record e he hrecord hct)
    apply ratio_ge_of_large hy _ hEpos
    -- `y/(c-2y) ≤ ⌈…⌉₊ ≤ E`
    have h1 : (⌈y / (c - 2 * y)⌉₊ : ℝ) ≤ E := by
      have : ⌈y / (c - 2 * y)⌉₊ ≤ E := le_trans (by omega) (le_trans (Nat.le_max_left _ _) hEN)
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h1

/-- **No lower density `1` when records are dense (Erdős #197, partial).** Under the same
hypothesis (an avoiding enumeration with records of rank `≥ c · value` occurring arbitrarily
late, `c > 0`), the set `S` has lower density at most `1 - c/2 < 1`; in particular
`lowerDensity S < 1`. So such an `S` cannot be a witness to `β(3) = 1`. -/
theorem lowerDensity_le_of_records_dense {c : ℝ} (hc : 0 < c) (e : ℕ ≃ S)
    (he : ¬ HasMonotoneAP (fun n => (e n : ℕ)) 3)
    (hrec : ∀ N, ∃ t, N ≤ t ∧ IsRecord e t ∧ c * (e t : ℕ) ≤ t) :
    lowerDensity S ≤ 1 - c / 2 ∧ lowerDensity S < 1 := by
  have hkey : c / 2 ≤ upperDensity Sᶜ :=
    upperDensity_compl_ge_of_records_dense e he hrec
  -- `upperDensity Sᶜ + lowerDensity S = 1` (apply the identity to `A = Sᶜ`, using `Sᶜᶜ = S`)
  have hid : upperDensity Sᶜ + lowerDensity S = 1 := by
    have := upperDensity_add_lowerDensity_compl Sᶜ
    rwa [compl_compl] at this
  constructor <;> linarith

end PermutationMonotoneAP
