import Erdos.PermutationMonotoneAP.Statement
import Erdos.PermutationMonotoneAP.Dyadic
import Mathlib.Order.KonigLemma

/-!
# A compactness bridge for Erdős #196 (the 4-AP question)

We reduce #196 — *does ℕ admit a permutation with no monotone 4-term AP?* — to a
**finitary** statement: the existence of 4-AP-free orders of every initial segment
`[0,N)` under a single *uniform* displacement bound.

Think of an order on ℕ as a rank assignment `σ : ℕ → ℕ` (`σ v` = the position of value
`v`). The order is *type ω* exactly when every value has finitely many predecessors. A
*uniform* bound `σ v ≤ f v` guarantees this for free: `{u | σ u < σ v}` injects into
`{0,…,f v − 1}` (as `σ` is injective), so it is finite. Hence:

> **`FiniteFeasible f`** (4-AP-free injective orders of `[0,N)` with `σ v ≤ f v`, for all `N`)
> **⟹ `Erdos196Avoidable`** (a 4-AP-avoiding permutation of ℕ exists).

The proof threads the finite orders into a global `σ : ℕ → ℕ` by König's lemma
(`exists_seq_forall_proj_of_forall_finite`), then compresses `σ` to a genuine
permutation `ℕ ≃ ℕ` of order type ω, which inherits 4-AP-freeness.

Without the *uniform* `f`, compactness only yields a *dense* 4-AP-free order (e.g. van
der Corput); the uniform bound is exactly what forces order type ω. This is the precise
content of "the obstruction in #196 is purely the order type" — and it makes the problem
**construction-ready**: any uniform-bound finite construction (or an inductive existence
proof) yields #196 via this bridge.
-/

namespace PermutationMonotoneAP

open Function

/-- `σ : ℕ → ℕ` has a monotone 4-term AP below `N`: some AP `a, a+d, a+2d, a+3d`
(`d ≥ 1`, `a+3d < N`) whose `σ`-values are strictly monotone. -/
def HasMono4 (σ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + 3 * d < N ∧
    ((σ a < σ (a + d) ∧ σ (a + d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + 3 * d)) ∨
     (σ (a + 3 * d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + d) ∧ σ (a + d) < σ a))

/-- **Finite feasibility with uniform displacement bound `f`.** For every `N` there is
an injective rank assignment on `[0,N)` bounded by `f` and free of monotone 4-APs. -/
def FiniteFeasible (f : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ σ : ℕ → ℕ, Set.InjOn σ (Set.Iio N) ∧ (∀ v < N, σ v ≤ f v) ∧ ¬ HasMono4 σ N

/-- A single AP `a, a+d, a+2d, a+3d` is `σ`-monotone (strictly increasing or strictly
decreasing). -/
def Mono4 (σ : ℕ → ℕ) (a d : ℕ) : Prop :=
  (σ a < σ (a + d) ∧ σ (a + d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + 3 * d)) ∨
  (σ (a + 3 * d) < σ (a + 2 * d) ∧ σ (a + 2 * d) < σ (a + d) ∧ σ (a + d) < σ a)

theorem hasMono4_iff (σ : ℕ → ℕ) (N : ℕ) :
    HasMono4 σ N ↔ ∃ a d : ℕ, 0 < d ∧ a + 3 * d < N ∧ Mono4 σ a d := Iff.rfl

/-! ### Stage A: a global `σ : ℕ → ℕ` via König's lemma. -/

/-- Extend a partial assignment `g : Fin N → ℕ` to all of `ℕ` by `0` outside `[0,N)`. -/
def extend {N : ℕ} (g : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then g ⟨n, h⟩ else 0

theorem extend_apply {N : ℕ} (g : Fin N → ℕ) (n : ℕ) (h : n < N) :
    extend g n = g ⟨n, h⟩ := dif_pos h

/-- The level type for König's lemma at stage `N`: an injective rank assignment of the
initial segment `Fin N`, bounded pointwise by `f`, and free of monotone 4-APs. -/
def Level (f : ℕ → ℕ) (N : ℕ) : Type :=
  { g : Fin N → ℕ // Function.Injective g ∧ (∀ v : Fin N, g v ≤ f v.val) ∧
      ∀ a d : ℕ, 0 < d → a + 3 * d < N → ¬ Mono4 (extend g) a d }

instance instFiniteLevel (f : ℕ → ℕ) (N : ℕ) : Finite (Level f N) := by
  have hbase : Finite { g : Fin N → ℕ // ∀ v : Fin N, g v ≤ f v.val } := by
    apply Finite.of_injective
      (β := ∀ v : Fin N, Fin (f v.val + 1))
      (fun g v => ⟨g.val v, Nat.lt_succ_of_le (g.property v)⟩)
    intro g g' hgg'
    apply Subtype.ext
    funext v
    have := congrFun hgg' v
    simpa using congrArg Fin.val this
  -- `Level f N` is a subtype of the finite type `{ g // ∀ v, g v ≤ f v }`.
  apply Finite.of_injective
    (β := { g : Fin N → ℕ // ∀ v : Fin N, g v ≤ f v.val })
    (fun L => ⟨L.val, L.property.2.1⟩)
  intro L L' h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext h

/-- `Mono4` depends only on the values of `σ` at `a, a+d, a+2d, a+3d`. -/
theorem mono4_congr {σ τ : ℕ → ℕ} {a d : ℕ}
    (h0 : σ a = τ a) (h1 : σ (a + d) = τ (a + d))
    (h2 : σ (a + 2 * d) = τ (a + 2 * d)) (h3 : σ (a + 3 * d) = τ (a + 3 * d)) :
    Mono4 σ a d ↔ Mono4 τ a d := by
  unfold Mono4; rw [h0, h1, h2, h3]

/-- From a finite feasible witness at stage `N`, the level type `Level f N` is nonempty. -/
theorem nonempty_level_of_finiteFeasible (f : ℕ → ℕ) (h : FiniteFeasible f) (N : ℕ) :
    Nonempty (Level f N) := by
  obtain ⟨σ, hinj, hbound, hfree⟩ := h N
  refine ⟨⟨fun v => σ v.val, ?_, ?_, ?_⟩⟩
  · -- injective from `InjOn σ (Iio N)`
    intro v w hvw
    exact Fin.ext (hinj (Set.mem_Iio.mpr v.isLt) (Set.mem_Iio.mpr w.isLt) hvw)
  · -- pointwise bound
    intro v
    exact hbound v.val v.isLt
  · -- 4-AP-freeness transfers from `σ`
    intro a d hd h3 hmono
    refine hfree ⟨a, d, hd, h3, ?_⟩
    -- `extend g` agrees with `σ` on the four indices (all `< N`)
    have ha : a < N := by omega
    have had : a + d < N := by omega
    have ha2 : a + 2 * d < N := by omega
    have e0 : extend (fun v : Fin N => σ v.val) a = σ a := by
      rw [extend_apply _ _ ha]
    have e1 : extend (fun v : Fin N => σ v.val) (a + d) = σ (a + d) := by
      rw [extend_apply _ _ had]
    have e2 : extend (fun v : Fin N => σ v.val) (a + 2 * d) = σ (a + 2 * d) := by
      rw [extend_apply _ _ ha2]
    have e3 : extend (fun v : Fin N => σ v.val) (a + 3 * d) = σ (a + 3 * d) := by
      rw [extend_apply _ _ h3]
    exact (mono4_congr e0 e1 e2 e3).mp hmono

/-- The König projection: restrict a level at stage `j` to a level at stage `i ≤ j`,
by precomposing with `Fin.castLE`. -/
def levelProj (f : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) (L : Level f j) : Level f i := by
  refine ⟨fun v => L.val (Fin.castLE hij v), ?_, ?_, ?_⟩
  · -- injective: castLE injective, L.val injective
    intro v w hvw
    exact Fin.castLE_injective hij (L.property.1 hvw)
  · -- bound: castLE preserves underlying value
    intro v
    have hb := L.property.2.1 (Fin.castLE hij v)
    simpa using hb
  · -- 4-AP-freeness pulls back: the two extensions agree on `[0,i)`
    intro a d hd h3 hmono
    have h3j : a + 3 * d < j := lt_of_lt_of_le h3 hij
    refine L.property.2.2 a d hd h3j ?_
    -- agreement of extensions on the four indices (all `< i ≤ j`)
    have agree : ∀ n : ℕ, n < i →
        extend (fun v : Fin i => L.val (Fin.castLE hij v)) n = extend L.val n := by
      intro n hn
      rw [extend_apply _ _ hn, extend_apply _ _ (lt_of_lt_of_le hn hij)]
      rfl
    have e0 := agree a (by omega)
    have e1 := agree (a + d) (by omega)
    have e2 := agree (a + 2 * d) (by omega)
    have e3 := agree (a + 3 * d) h3
    exact (mono4_congr e0 e1 e2 e3).mp hmono

theorem levelProj_refl (f : ℕ → ℕ) {i : ℕ} (L : Level f i) :
    levelProj f (le_refl i) L = L := by
  apply Subtype.ext
  funext v
  rfl

theorem levelProj_trans (f : ℕ → ℕ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (L : Level f k) :
    levelProj f hij (levelProj f hjk L) = levelProj f (hij.trans hjk) L := by
  apply Subtype.ext
  funext v
  rfl

/-- **Stage A.** From finite feasibility, König's lemma threads the finite levels into a
single global rank assignment `σ : ℕ → ℕ`: injective, bounded by `f`, and free of all
monotone 4-APs (at every scale `N`). -/
theorem global_sigma (f : ℕ → ℕ) (h : FiniteFeasible f) :
    ∃ σ : ℕ → ℕ, Function.Injective σ ∧ (∀ v, σ v ≤ f v) ∧ ∀ N, ¬ HasMono4 σ N := by
  -- instances for König
  haveI : Finite (Level f 0) := instFiniteLevel f 0
  haveI : ∀ i, Nonempty (Level f i) := fun i => nonempty_level_of_finiteFeasible f h i
  -- apply König's infinity lemma
  obtain ⟨F, hF⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun i => Level f i)
    (π := fun {i j} hij L => levelProj f hij L)
    (fun {i} a => levelProj_refl f a)
    (fun {i j k} hij hjk a => levelProj_trans f hij hjk a)
    (fun i a => Set.toFinite _)
  -- the global rank assignment
  set σ : ℕ → ℕ := fun v => (F (v + 1)).val ⟨v, Nat.lt_succ_self v⟩ with hσ
  -- compatibility: for any window `j > v`, the level `F j` reports `σ v` at index `v`.
  have compat : ∀ v j : ℕ, ∀ hv : v < j, (F j).val ⟨v, hv⟩ = σ v := by
    intro v j hv
    have hle : v + 1 ≤ j := hv
    have hproj := hF hle
    -- `levelProj f hle (F j)` at `⟨v, _⟩` is `(F j).val ⟨v, hv⟩`
    have hc := congrArg (fun L => (L.val ⟨v, Nat.lt_succ_self v⟩)) hproj
    simpa [levelProj, σ] using hc
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- injectivity: compare inside a single level large enough to contain both indices
    intro u v huv
    set N := max u v + 1 with hN
    have hu : u < N := by omega
    have hv : v < N := by omega
    have eu : (F N).val ⟨u, hu⟩ = σ u := compat u N hu
    have ev : (F N).val ⟨v, hv⟩ = σ v := compat v N hv
    have : (F N).val ⟨u, hu⟩ = (F N).val ⟨v, hv⟩ := by rw [eu, ev, huv]
    have := (F N).property.1 this
    exact congrArg Fin.val this
  · -- pointwise bound
    intro v
    have hb := (F (v + 1)).property.2.1 ⟨v, Nat.lt_succ_self v⟩
    simpa [σ] using hb
  · -- 4-AP-freeness at every scale
    intro N hN
    obtain ⟨a, d, hd, h3, hmono⟩ := hN
    -- work inside level `F N`; all four indices are `< N`
    refine (F N).property.2.2 a d hd h3 ?_
    have agree : ∀ n : ℕ, n < N → extend (F N).val n = σ n := by
      intro n hn
      rw [extend_apply _ _ hn]
      exact compat n N hn
    have e0 := agree a (by omega)
    have e1 := agree (a + d) (by omega)
    have e2 := agree (a + 2 * d) (by omega)
    have e3 := agree (a + 3 * d) h3
    exact (mono4_congr e0 e1 e2 e3).mpr hmono

/-! ### Stage B: compress `σ` to a genuine permutation of order type ω.

Given the global `σ` (injective, free of all monotone 4-APs), the σ-order
`u ≺ v ↔ σ u < σ v` is a well-order of type ω: every value has only finitely many
σ-predecessors (they inject into `Set.Iio (σ v)`). The **rank** `ρ v := |{u | σ u < σ v}|`
is the order-isomorphism to ℕ. We show `ρ` is bijective and that the inverse permutation
inherits 4-AP-freeness. -/

/-- The set of σ-predecessors of `v` is finite: `σ` injects it into `Set.Iio (σ v)`. -/
theorem finite_sigmaLt {σ : ℕ → ℕ} (hinj : Function.Injective σ) (v : ℕ) :
    {u | σ u < σ v}.Finite := by
  apply Set.Finite.ofFinset (Finset.range (σ v) |>.preimage σ (hinj.injOn))
  intro u
  simp only [Finset.mem_preimage, Finset.mem_range, Set.mem_setOf_eq]

/-- The **σ-rank** of `v`: the number of values strictly below `v` in the σ-order. -/
noncomputable def rank (σ : ℕ → ℕ) (v : ℕ) : ℕ := {u | σ u < σ v}.ncard

/-- **Rank is strictly monotone in the σ-order.** If `σ u < σ v` then `rank σ u < rank σ v`,
because the σ-predecessors of `u` form a proper subset of those of `v` (the latter also
contains `u` itself). -/
theorem rank_lt_rank {σ : ℕ → ℕ} (hinj : Function.Injective σ) {u v : ℕ}
    (huv : σ u < σ v) : rank σ u < rank σ v := by
  have hsub : {w | σ w < σ u} ⊆ {w | σ w < σ v} := fun w hw =>
    lt_trans hw huv
  have hu_not : u ∉ {w | σ w < σ u} := by simp [Set.mem_setOf_eq]
  have hu_in : u ∈ {w | σ w < σ v} := huv
  have hssub : {w | σ w < σ u} ⊂ {w | σ w < σ v} :=
    ⟨hsub, fun hcon => hu_not (hcon hu_in)⟩
  exact Set.ncard_lt_ncard hssub (finite_sigmaLt hinj v)

/-- **Rank is injective:** distinct values have distinct σ-values (σ injective), and the
σ-order is total, so their ranks differ by `rank_lt_rank`. -/
theorem rank_injective {σ : ℕ → ℕ} (hinj : Function.Injective σ) :
    Function.Injective (rank σ) := by
  intro u v huv
  rcases lt_trichotomy (σ u) (σ v) with h | h | h
  · exact absurd huv (rank_lt_rank hinj h).ne
  · exact hinj h
  · exact absurd huv.symm (rank_lt_rank hinj h).ne

/-- **The range of `rank` is downward closed.** For any `m < rank σ v`, there is a value
`u` with `rank σ u = m`. Indeed `rank` maps the σ-predecessors of `v` injectively into
`Set.Iio (rank σ v)`, and since `|{u | σ u < σ v}| = rank σ v = |Iio (rank σ v)|`, this map
is onto the initial segment. -/
theorem rank_range_downward {σ : ℕ → ℕ} (hinj : Function.Injective σ) {v m : ℕ}
    (hm : m < rank σ v) : ∃ u, rank σ u = m := by
  have hfin : {u | σ u < σ v}.Finite := finite_sigmaLt hinj v
  -- `rank` maps σ-predecessors of `v` into `Iio (rank σ v)`, injectively, with equal card.
  have hmaps : ∀ u ∈ {u | σ u < σ v}, rank σ u ∈ Set.Iio (rank σ v) := by
    intro u hu; exact rank_lt_rank hinj hu
  have hinjon : ∀ (a₁ a₂ : ℕ), a₁ ∈ {u | σ u < σ v} → a₂ ∈ {u | σ u < σ v} →
      rank σ a₁ = rank σ a₂ → a₁ = a₂ :=
    fun a₁ a₂ _ _ heq => rank_injective hinj heq
  -- card of the target initial segment equals card of the predecessor set (= rank σ v)
  have hcard : (Set.Iio (rank σ v)).ncard ≤ ({u | σ u < σ v}).ncard := by
    rw [Set.ncard_Iio_nat]; exact le_of_eq rfl
  -- surjectivity onto the initial segment yields a preimage of `m`
  have htfin : (Set.Iio (rank σ v)).Finite := Set.finite_Iio _
  obtain ⟨u, _, hu⟩ := Set.surj_on_of_inj_on_of_ncard_le
    (s := {u | σ u < σ v}) (t := Set.Iio (rank σ v))
    (fun a _ => rank σ a) hmaps hinjon hcard htfin m (Set.mem_Iio.mpr hm)
  exact ⟨u, hu.symm⟩

/-- **Rank is surjective.** Its range is infinite (rank is injective and ℕ is infinite)
hence unbounded, and downward closed (`rank_range_downward`); an unbounded downward-closed
subset of ℕ is everything. -/
theorem rank_surjective {σ : ℕ → ℕ} (hinj : Function.Injective σ) :
    Function.Surjective (rank σ) := by
  intro n
  -- the range of `rank σ` is infinite
  have hrange_inf : (Set.range (rank σ)).Infinite :=
    Set.infinite_range_of_injective (rank_injective hinj)
  -- hence it has an element `> n`
  obtain ⟨b, hb_mem, hb_gt⟩ := hrange_inf.exists_gt n
  obtain ⟨v, hv⟩ := hb_mem
  -- `n < b = rank σ v`, so downward closure gives a preimage of `n`
  have : n < rank σ v := by rw [hv]; exact hb_gt
  exact rank_range_downward hinj this

/-- **The compactness bridge for Erdős #196.** If, for some uniform bound `f`, every
initial segment `[0,N)` admits an injective 4-AP-free order with `σ v ≤ f v`, then ℕ
admits a permutation avoiding all monotone 4-APs. -/
theorem erdos196Avoidable_of_finiteFeasible (f : ℕ → ℕ) (h : FiniteFeasible f) :
    Erdos196Avoidable := by
  -- Stage A: the global rank assignment.
  obtain ⟨σ, hinj, _hbound, hfree⟩ := global_sigma f h
  -- The σ-order and the rank order coincide.
  have rank_iff : ∀ u v : ℕ, rank σ u < rank σ v ↔ σ u < σ v := by
    intro u v
    constructor
    · intro hr
      rcases lt_trichotomy (σ u) (σ v) with h' | h' | h'
      · exact h'
      · exact absurd (congrArg (rank σ) (hinj h')) hr.ne
      · exact absurd (rank_lt_rank hinj h') (not_lt.mpr hr.le)
    · exact rank_lt_rank hinj
  -- The permutation: value ↦ σ-rank.
  set e : ℕ ≃ ℕ := Equiv.ofBijective (rank σ) ⟨rank_injective hinj, rank_surjective hinj⟩
    with he
  -- `rank σ (e.symm n) = n` for all `n` (the inverse identity).
  have hrank_symm : ∀ n, rank σ (e.symm n) = n := by
    intro n
    have : e (e.symm n) = n := e.apply_symm_apply n
    simpa [he, Equiv.ofBijective] using this
  -- Use `e.symm` as the position → value permutation.
  refine ⟨e.symm, ?_⟩
  intro hmono
  obtain ⟨p, hp, a, d, hAP⟩ := hmono
  -- The four AP values, indexed by the positions.
  set v₀ := e.symm (p 0) with hv0
  set v₁ := e.symm (p 1) with hv1
  set v₂ := e.symm (p 2) with hv2
  set v₃ := e.symm (p 3) with hv3
  -- σ-values are strictly increasing along the (strictly increasing) positions:
  -- positions = ranks, and ranks-order = σ-order.
  have hσ01 : σ v₀ < σ v₁ := by
    rw [← rank_iff]; rw [hv0, hv1, hrank_symm, hrank_symm]; exact hp (by norm_num)
  have hσ12 : σ v₁ < σ v₂ := by
    rw [← rank_iff]; rw [hv1, hv2, hrank_symm, hrank_symm]; exact hp (by norm_num)
  have hσ23 : σ v₂ < σ v₃ := by
    rw [← rank_iff]; rw [hv2, hv3, hrank_symm, hrank_symm]; exact hp (by norm_num)
  -- The integer AP relations at j = 0,1,2,3.
  have hA0 : (v₀ : ℤ) = a := by have := hAP 0 (by norm_num); simpa using this
  have hA1 : (v₁ : ℤ) = a + d := by have := hAP 1 (by norm_num); simpa using this
  have hA2 : (v₂ : ℤ) = a + 2 * d := by
    have := hAP 2 (by norm_num); simpa using this
  have hA3 : (v₃ : ℤ) = a + 3 * d := by
    have := hAP 3 (by norm_num); simpa using this
  -- The four values are distinct (σ-values are distinct), so `d ≠ 0`.
  have hne01 : v₀ ≠ v₁ := fun heq => absurd (heq ▸ hσ01) (lt_irrefl _)
  have hd0 : d ≠ 0 := by
    intro hd; apply hne01
    have : (v₀ : ℤ) = (v₁ : ℤ) := by rw [hA0, hA1, hd]; ring
    exact Nat.cast_injective this
  rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
  · -- `d < 0`: the AP decreases; base it at `v₃` with step `δ = -d`.
    set δ : ℕ := (-d).toNat with hδ
    have hδpos : 0 < δ := by
      rw [hδ]; omega
    have hδcast : (δ : ℤ) = -d := by rw [hδ]; omega
    -- nat identities `v₂ = v₃ + δ`, `v₁ = v₃ + 2δ`, `v₀ = v₃ + 3δ`
    have e2 : v₂ = v₃ + δ := by
      have : (v₂ : ℤ) = (v₃ : ℤ) + δ := by rw [hA2, hA3, hδcast]; ring
      exact_mod_cast this
    have e1 : v₁ = v₃ + 2 * δ := by
      have : (v₁ : ℤ) = (v₃ : ℤ) + 2 * δ := by rw [hA1, hA3, hδcast]; ring
      exact_mod_cast this
    have e0 : v₀ = v₃ + 3 * δ := by
      have : (v₀ : ℤ) = (v₃ : ℤ) + 3 * δ := by rw [hA0, hA3, hδcast]; ring
      exact_mod_cast this
    -- exhibit a decreasing σ-monotone 4-AP based at `v₃`
    refine hfree (v₃ + 3 * δ + 1) ⟨v₃, δ, hδpos, by omega, Or.inr ?_⟩
    rw [← e0, ← e1, ← e2]
    exact ⟨hσ01, hσ12, hσ23⟩
  · -- `d > 0`: the AP increases; base it at `v₀` with step `δ = d`.
    set δ : ℕ := d.toNat with hδ
    have hδpos : 0 < δ := by rw [hδ]; omega
    have hδcast : (δ : ℤ) = d := by rw [hδ]; omega
    have e1 : v₁ = v₀ + δ := by
      have : (v₁ : ℤ) = (v₀ : ℤ) + δ := by rw [hA1, hA0, hδcast]
      exact_mod_cast this
    have e2 : v₂ = v₀ + 2 * δ := by
      have : (v₂ : ℤ) = (v₀ : ℤ) + 2 * δ := by rw [hA2, hA0, hδcast]
      exact_mod_cast this
    have e3 : v₃ = v₀ + 3 * δ := by
      have : (v₃ : ℤ) = (v₀ : ℤ) + 3 * δ := by rw [hA3, hA0, hδcast]
      exact_mod_cast this
    -- exhibit an increasing σ-monotone 4-AP based at `v₀`
    refine hfree (v₀ + 3 * δ + 1) ⟨v₀, δ, hδpos, by omega, Or.inl ?_⟩
    rw [← e1, ← e2, ← e3]
    exact ⟨hσ01, hσ12, hσ23⟩

/-- Packaged form: it suffices to exhibit *some* uniform bound under which all finite
initial segments are 4-AP-free-orderable. -/
theorem erdos196Avoidable_of_exists_finiteFeasible
    (h : ∃ f : ℕ → ℕ, FiniteFeasible f) : Erdos196Avoidable := by
  obtain ⟨f, hf⟩ := h
  exact erdos196Avoidable_of_finiteFeasible f hf

/-! ### The reverse direction: the reduction is tight.

If a 4-AP-avoiding permutation `g` exists, then `f := g.symm` (value ↦ position) is a
uniform displacement bound witnessing `FiniteFeasible`: each initial segment `[0,N)` is
ordered by `g.symm` itself, which is injective, meets the bound with equality, and is
4-AP-free because `g` is. Hence `∃ f, FiniteFeasible f` is an **exact** finitary
restatement of `Erdos196Avoidable` — there is no slack between the finitary search and
the genuine problem. -/

/-- Four positions `q0 < q1 < q2 < q3` whose `g`-values form an arithmetic progression
constitute a monotone 4-AP of the permutation `g`. (The increasing/decreasing sign of the
AP is carried by the common difference `d'`.) -/
theorem hasMonotoneAP_four_of_positions {g : ℕ ≃ ℕ} {q0 q1 q2 q3 : ℕ}
    (h01 : q0 < q1) (h12 : q1 < q2) (h23 : q2 < q3)
    {a' d' : ℤ} (hv0 : (g q0 : ℤ) = a') (hv1 : (g q1 : ℤ) = a' + d')
    (hv2 : (g q2 : ℤ) = a' + 2 * d') (hv3 : (g q3 : ℤ) = a' + 3 * d') :
    HasMonotoneAP (fun n => (g n : ℕ)) 4 := by
  refine ⟨fun j => match j with | 0 => q0 | 1 => q1 | 2 => q2 | (n + 3) => q3 + n,
          ?_, a', d', ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact h01
    | 1 => exact h12
    | 2 => simpa using h23
    | (n + 3) => simp only; omega
  · intro j hj
    interval_cases j
    · simpa using hv0
    · simpa using hv1
    · simpa using hv2
    · simpa using hv3

/-- **Reverse bridge.** A 4-AP-avoiding permutation of ℕ yields a uniform bound `f` (namely
`g.symm`) under which every initial segment is feasible. -/
theorem exists_finiteFeasible_of_erdos196Avoidable (h : Erdos196Avoidable) :
    ∃ f : ℕ → ℕ, FiniteFeasible f := by
  obtain ⟨g, hg⟩ := h
  refine ⟨(g.symm : ℕ → ℕ), fun N => ⟨(g.symm : ℕ → ℕ), ?_, ?_, ?_⟩⟩
  · exact fun u _ v _ huv => g.symm.injective huv
  · exact fun v _ => le_refl _
  · rintro ⟨a, d, _hd, _h3, hcase⟩
    apply hg
    rcases hcase with ⟨H01, H12, H23⟩ | ⟨H01, H12, H23⟩
    · -- increasing AP `a, a+d, a+2d, a+3d`, positions ascending
      exact hasMonotoneAP_four_of_positions H01 H12 H23
        (a' := (a : ℤ)) (d' := (d : ℤ))
        (by rw [Equiv.apply_symm_apply])
        (by rw [Equiv.apply_symm_apply]; push_cast; ring)
        (by rw [Equiv.apply_symm_apply]; push_cast; ring)
        (by rw [Equiv.apply_symm_apply]; push_cast; ring)
    · -- decreasing AP: re-base at `a+3d` with step `-d` so positions ascend
      exact hasMonotoneAP_four_of_positions H01 H12 H23
        (a' := (a : ℤ) + 3 * d) (d' := -(d : ℤ))
        (by rw [Equiv.apply_symm_apply]; push_cast; ring)
        (by rw [Equiv.apply_symm_apply]; push_cast; ring)
        (by rw [Equiv.apply_symm_apply]; push_cast; ring)
        (by rw [Equiv.apply_symm_apply]; ring)

/-- **The finitary characterisation of Erdős #196.** A permutation of ℕ avoiding all
monotone 4-term APs exists **iff** there is a uniform displacement bound `f` under which
every initial segment `[0,N)` admits an injective 4-AP-free order bounded by `f`. The
forward direction is König + rank-compression (`erdos196Avoidable_of_finiteFeasible`); the
reverse takes `f = g.symm`. This pins the open content of #196 as a purely finitary search
for a single uniform bound. -/
theorem exists_finiteFeasible_iff_avoidable :
    (∃ f : ℕ → ℕ, FiniteFeasible f) ↔ Erdos196Avoidable :=
  ⟨erdos196Avoidable_of_exists_finiteFeasible, exists_finiteFeasible_of_erdos196Avoidable⟩

/-! ### A forced necessary condition: unbounded displacement (the drift lemma).

The uniform bound `f` sought by the bridge cannot stay close to the identity. If the order's
displacement `|σ v − v|` is bounded by a constant `C`, then every AP of common difference
`d > 2 C` is placed in strictly increasing position order (each term moves by less than half a
step), producing arbitrarily long monotone APs. So a 4-AP avoider must **drift** — its bound
satisfies `f v − v → ∞` — while still keeping each value at a finite position (order type ω).
That tension is exactly what a #196 construction has to resolve, and it is why the bound `f`
cannot be anything as simple as `f = id`. -/

/-- If `g.symm` (value ↦ position) has displacement bounded by `C`, then `g` has a monotone
4-AP: the AP `0, d, 2d, 3d` with `d = 2 C + 1` has strictly ascending positions, because each
term's position is within `C` of its value and the gap `d` exceeds `2 C`. The four ascending
positions feed `hasMonotoneAP_four_of_positions`. -/
theorem hasMonotoneAP_four_of_bounded_displacement (g : ℕ ≃ ℕ) (C : ℕ)
    (hbd : ∀ v : ℕ, ((g.symm v : ℤ) - v).natAbs ≤ C) :
    HasMonotoneAP (fun n => (g n : ℕ)) 4 := by
  set d : ℕ := 2 * C + 1 with hd
  -- Two-sided integer bounds `v - C ≤ σ v ≤ v + C` from the displacement bound.
  have hbnd : ∀ v : ℕ, (v : ℤ) - C ≤ (g.symm v : ℤ) ∧ (g.symm v : ℤ) ≤ (v : ℤ) + C := by
    intro v
    have h : |((g.symm v : ℤ) - v)| ≤ (C : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hbd v
    have hpair := abs_le.mp h
    exact ⟨by linarith [hpair.1], by linarith [hpair.2]⟩
  have h01 : g.symm 0 < g.symm d := by
    have a0 := (hbnd 0).2; have ad := (hbnd d).1; omega
  have h12 : g.symm d < g.symm (2 * d) := by
    have a1 := (hbnd d).2; have a2 := (hbnd (2 * d)).1; omega
  have h23 : g.symm (2 * d) < g.symm (3 * d) := by
    have a2 := (hbnd (2 * d)).2; have a3 := (hbnd (3 * d)).1; omega
  exact hasMonotoneAP_four_of_positions h01 h12 h23
    (a' := 0) (d' := (d : ℤ))
    (by rw [Equiv.apply_symm_apply]; norm_num)
    (by rw [Equiv.apply_symm_apply]; ring)
    (by rw [Equiv.apply_symm_apply]; push_cast; ring)
    (by rw [Equiv.apply_symm_apply]; push_cast; ring)

/-- **Drift is forced (Erdős #196).** Every permutation of ℕ avoiding all monotone 4-APs has
unbounded displacement: for each `C` some value lies more than `C` from its position. Combined
with the compactness bridge, the witnessing bound `f` must drift (`f v − v` unbounded) yet keep
every value at a finite position — the precise, simultaneous demand a #196 construction faces. -/
theorem unbounded_displacement_of_avoiding (g : ℕ ≃ ℕ)
    (hg : ¬ HasMonotoneAP (fun n => (g n : ℕ)) 4) (C : ℕ) :
    ∃ v : ℕ, C < ((g.symm v : ℤ) - v).natAbs := by
  by_contra h
  exact hg (hasMonotoneAP_four_of_bounded_displacement g C
    (fun v => not_lt.mp (fun hlt => h ⟨v, hlt⟩)))

end PermutationMonotoneAP
