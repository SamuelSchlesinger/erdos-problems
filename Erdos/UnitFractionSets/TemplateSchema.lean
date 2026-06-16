/-
# Generic Template Schema for Problem #301

This file isolates the reusable theorem pattern behind the concrete multiplier
gadgets in `UpperBound.lean` and `DenseTemplate.lean`.

The schema has three independent pieces:

* a finite hypergraph hitting lemma;
* a generic scaled reciprocal-identity obstruction for sum-free sets;
* a common-denominator certificate lemma for checking identities with integer
  arithmetic.

The point is to make future density improvements mostly data: multipliers,
finite reciprocal edges, a finite hitting certificate, and p-adic disjointness.
-/
import Erdos.UnitFractionSets.Statement

namespace UnitFractionSets

open scoped BigOperators

/-- A finite multiplier gadget, indexed by a finite prefix `P`. -/
def TemplateGadget {V : Type*} (mul : V → ℕ) (P : Finset V) (a : ℕ) :
    Finset ℕ :=
  P.image fun v => mul v * a

/-- Finite hypergraph hitting lemma: if every too-large subset of `P` contains
one of the forbidden edges, and each forbidden edge cannot be fully present in
`A` after applying `f`, then `A` keeps at most `keep` points from `P.image f`. -/
theorem hypergraph_hitting_image_inter_card_le {V β : Type*} [DecidableEq β]
    (P : Finset V) (A : Finset β) (f : V → β) (badEdges : Finset (Finset V))
    (keep : ℕ) (hf : Function.Injective f)
    (hForbidden : ∀ E ∈ badEdges, (∀ v ∈ E, f v ∈ A) → False)
    (hHit : ∀ S : Finset V, S ⊆ P → keep < S.card → ∃ E ∈ badEdges, E ⊆ S) :
    (P.image f ∩ A).card ≤ keep := by
  let S : Finset V := P.filter fun v => f v ∈ A
  have himage : S.image f = P.image f ∩ A := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩,
          (Finset.mem_filter.mp hv).2⟩
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyP, hyA⟩
      rcases Finset.mem_image.mp hyP with ⟨v, hvP, rfl⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hvP, hyA⟩, rfl⟩
  have hcard : S.card = (P.image f ∩ A).card := by
    calc
      S.card = (S.image f).card := (Finset.card_image_of_injective S hf).symm
      _ = (P.image f ∩ A).card := by rw [himage]
  by_contra hle
  have hgt : keep < S.card := by
    rw [hcard]
    exact Nat.lt_of_not_ge hle
  obtain ⟨E, hE, hES⟩ := hHit S (Finset.filter_subset _ _) hgt
  exact hForbidden E hE fun v hv => (Finset.mem_filter.mp (hES hv)).2

/-- A finite set contains one of the listed hyperedges. -/
def ContainsHyperedge {V : Type*} (badEdges : Finset (Finset V)) (S : Finset V) : Prop :=
  ∃ E ∈ badEdges, E ⊆ S

private theorem containsHyperedge_mono {V : Type*} {badEdges : Finset (Finset V)}
    {S T : Finset V} (hST : S ⊆ T) :
    ContainsHyperedge badEdges S → ContainsHyperedge badEdges T := by
  rintro ⟨E, hE, hES⟩
  exact ⟨E, hE, hES.trans hST⟩

/-- Executable branch search for finite prefix hitting.

`finiteBranchSearch edgePresent xs need chosen = false` means that every way of
adding exactly `need` vertices from `xs` to `chosen` is forced to contain an
edge, provided `edgePresent` is a sound executable detector for listed edges.

This is intentionally generic.  Concrete files may implement `edgePresent`
using bit masks or generated tables, while this theorem supplies the proof
interface from branch certificates to the usual prefix-hitting statement. -/
def finiteBranchSearch {V : Type*} [DecidableEq V] (edgePresent : Finset V → Bool) :
    List V → ℕ → Finset V → Bool
  | [], need, chosen => if edgePresent chosen then false else decide (need = 0)
  | x :: xs, need, chosen =>
      if edgePresent chosen then false
      else if need = 0 then true
      else if xs.length + 1 < need then false
      else finiteBranchSearch edgePresent xs need chosen ||
        finiteBranchSearch edgePresent xs (need - 1) (insert x chosen)

theorem finiteBranchSearch_complete {V : Type*} [DecidableEq V]
    {badEdges : Finset (Finset V)} {edgePresent : Finset V → Bool}
    (hedgePresent :
      ∀ S : Finset V, edgePresent S = true → ContainsHyperedge badEdges S)
    {xs : List V} {need : ℕ} {chosen extra : Finset V}
    (hsearch : finiteBranchSearch edgePresent xs need chosen = false)
    (hextra : extra ⊆ xs.toFinset)
    (hdisj : Disjoint chosen extra)
    (hcard : extra.card = need) :
    ContainsHyperedge badEdges (chosen ∪ extra) := by
  induction xs generalizing need chosen extra with
  | nil =>
      by_cases hedge : edgePresent chosen = true
      · exact containsHyperedge_mono Finset.subset_union_left
          (hedgePresent chosen hedge)
      · have hcard_zero : extra.card = 0 := by
          have hle : extra.card ≤ ([].toFinset : Finset V).card := Finset.card_le_card hextra
          simpa using hle
        have hextra_empty : extra = ∅ := Finset.card_eq_zero.mp hcard_zero
        have hneed : need = 0 := by omega
        subst extra
        simp [finiteBranchSearch, hedge, hneed] at hsearch
  | cons x xs ih =>
      by_cases hedge : edgePresent chosen = true
      · exact containsHyperedge_mono Finset.subset_union_left
          (hedgePresent chosen hedge)
      · by_cases hneed0 : need = 0
        · have hextra_empty : extra = ∅ := by
            apply Finset.card_eq_zero.mp
            omega
          subst extra
          exfalso
          simp [finiteBranchSearch, hedge, hneed0] at hsearch
        · have hlen_not : ¬ xs.length + 1 < need := by
            intro hlt
            have hcard_le : extra.card ≤ (x :: xs).toFinset.card :=
              Finset.card_le_card hextra
            have hto : (x :: xs).toFinset.card ≤ xs.length + 1 := by
              simpa [Nat.add_comm] using List.toFinset_card_le (x :: xs)
            omega
          have hboth :
              finiteBranchSearch edgePresent xs need chosen = false ∧
                finiteBranchSearch edgePresent xs (need - 1) (insert x chosen) = false := by
            have hor :
                (finiteBranchSearch edgePresent xs need chosen ||
                  finiteBranchSearch edgePresent xs (need - 1) (insert x chosen)) = false := by
              simpa [finiteBranchSearch, hedge, hneed0, hlen_not] using hsearch
            simpa using
              (Bool.or_eq_false_eq_eq_false_and_eq_false
                (finiteBranchSearch edgePresent xs need chosen)
                (finiteBranchSearch edgePresent xs (need - 1) (insert x chosen))).mp hor
          have hleft : finiteBranchSearch edgePresent xs need chosen = false := hboth.1
          have hright : finiteBranchSearch edgePresent xs (need - 1) (insert x chosen) = false :=
            hboth.2
          by_cases hxextra : x ∈ extra
          · let extra' := extra.erase x
            have hsub : extra' ⊆ xs.toFinset := by
              intro y hy
              have hyextra : y ∈ extra := (Finset.mem_erase.mp hy).2
              have hyall := hextra hyextra
              simp only [List.toFinset_cons, Finset.mem_insert] at hyall
              rcases hyall with hyx | hyxs
              · have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
                exact (hyne hyx).elim
              · exact hyxs
            have hdisj' : Disjoint (insert x chosen) extra' := by
              rw [Finset.disjoint_left]
              intro y hyins hyextra'
              have hyextra : y ∈ extra := (Finset.mem_erase.mp hyextra').2
              simp only [Finset.mem_insert] at hyins
              rcases hyins with rfl | hychosen
              · exact (Finset.mem_erase.mp hyextra').1 rfl
              · exact (Finset.disjoint_left.mp hdisj hychosen) hyextra
            have hcard' : extra'.card = need - 1 := by
              rw [Finset.card_erase_of_mem hxextra]
              omega
            have hp' := ih hright hsub hdisj' hcard'
            have hunion : insert x chosen ∪ extra' = chosen ∪ extra := by
              ext y
              by_cases hyx : y = x
              · subst y
                simp [hxextra]
              · simp [extra', hyx, Finset.mem_erase]
            simpa [hunion] using hp'
          · have hsub : extra ⊆ xs.toFinset := by
              intro y hy
              have hyall := hextra hy
              simp only [List.toFinset_cons, Finset.mem_insert] at hyall
              rcases hyall with hyx | hyxs
              · subst y
                exact (hxextra hy).elim
              · exact hyxs
            exact ih hleft hsub hdisj hcard

theorem prefix_hitting_of_branch_search {V : Type*} [DecidableEq V]
    {badEdges : Finset (Finset V)} {edgePresent : Finset V → Bool}
    (hedgePresent :
      ∀ S : Finset V, edgePresent S = true → ContainsHyperedge badEdges S)
    {P : Finset V} {xs : List V} {keep : ℕ}
    (hxs : xs.toFinset = P)
    (hsearch : finiteBranchSearch edgePresent xs (keep + 1) ∅ = false) :
    ∀ S : Finset V, S ⊆ P → keep < S.card → ContainsHyperedge badEdges S := by
  intro S hS hcard
  obtain ⟨T, hTS, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := keep + 1) (Nat.succ_le_iff.mpr hcard)
  have hTlist : T ⊆ xs.toFinset := by
    rw [hxs]
    exact hTS.trans hS
  have hhit := finiteBranchSearch_complete hedgePresent
    (xs := xs) (need := keep + 1) (chosen := ∅) (extra := T)
    hsearch hTlist (by simp) hTcard
  exact containsHyperedge_mono (by simpa using hTS) hhit

/-! ### Bitmask branch search

`finiteBranchSearch` manipulates `Finset` values in its inner loop, which is
far too slow for closed-term evaluation.  The variants below carry the chosen
set as a natural-number bitmask and the candidate vertices as bit indices, so
every step of the search is plain `Nat` bitwise arithmetic — which the kernel
evaluates with GMP fast paths.  Certificates checked by `maskSearch` can
therefore be verified by `decide` instead of `native_decide`. -/

/-- The bitmask of a finite vertex set under the bit assignment `toBit`:
bit `toBit v` is set for each `v ∈ S`. -/
def maskOfFn {V : Type*} (toBit : V → ℕ) (S : Finset V) : ℕ :=
  S.fold (· ||| ·) 0 fun v => 1 <<< toBit v

@[simp] theorem maskOfFn_empty {V : Type*} (toBit : V → ℕ) :
    maskOfFn toBit (∅ : Finset V) = 0 :=
  Finset.fold_empty

/-- Bit `k` of `maskOfFn toBit S` is set exactly when some `v ∈ S` has
`toBit v = k`. -/
theorem testBit_maskOfFn {V : Type*} (toBit : V → ℕ) (S : Finset V) (k : ℕ) :
    (maskOfFn toBit S).testBit k = true ↔ ∃ v ∈ S, toBit v = k := by
  induction S using Finset.cons_induction with
  | empty => simp [maskOfFn]
  | cons x s hx ih =>
      have hfold : maskOfFn toBit (Finset.cons x s hx) =
          (1 <<< toBit x) ||| maskOfFn toBit s := Finset.fold_cons hx
      rw [hfold, Nat.testBit_or]
      simp only [Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
        decide_eq_true_eq, ih, Finset.mem_cons]
      constructor
      · rintro (rfl | ⟨v, hv, rfl⟩)
        · exact ⟨x, Or.inl rfl, rfl⟩
        · exact ⟨v, Or.inr hv, rfl⟩
      · rintro ⟨v, rfl | hv, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨v, hv, rfl⟩

/-- Inserting a vertex sets the corresponding bit.  No freshness hypothesis is
needed: if the vertex is already present, its bit is already set. -/
theorem maskOfFn_insert {V : Type*} [DecidableEq V] (toBit : V → ℕ) (x : V)
    (S : Finset V) :
    maskOfFn toBit (insert x S) = maskOfFn toBit S ||| 1 <<< toBit x := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [Bool.eq_iff_iff]
  simp only [testBit_maskOfFn, Nat.testBit_or, Bool.or_eq_true,
    Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq,
    Finset.mem_insert]
  constructor
  · rintro ⟨v, rfl | hv, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · exact ⟨v, Or.inr hv, rfl⟩
    · exact ⟨x, Or.inl rfl, rfl⟩

/-- For an injective bit assignment, mask containment characterizes set
containment. -/
theorem maskOfFn_land_eq_left_iff {V : Type*} {toBit : V → ℕ}
    (htoBit : Function.Injective toBit) {E S : Finset V} :
    maskOfFn toBit E &&& maskOfFn toBit S = maskOfFn toBit E ↔ E ⊆ S := by
  constructor
  · intro h v hv
    have hbit : (maskOfFn toBit E).testBit (toBit v) = true :=
      (testBit_maskOfFn toBit E (toBit v)).mpr ⟨v, hv, rfl⟩
    have hS := congrArg (fun n => n.testBit (toBit v)) h
    simp only [Nat.testBit_and, hbit, Bool.true_and] at hS
    obtain ⟨w, hw, hwv⟩ := (testBit_maskOfFn toBit S (toBit v)).mp hS
    exact htoBit hwv ▸ hw
  · intro hES
    refine Nat.eq_of_testBit_eq fun k => ?_
    rcases hE : (maskOfFn toBit E).testBit k with _ | _
    · simp [Nat.testBit_and, hE]
    · obtain ⟨v, hv, rfl⟩ := (testBit_maskOfFn toBit E k).mp hE
      simp [Nat.testBit_and, hE,
        (testBit_maskOfFn toBit S (toBit v)).mpr ⟨v, hES hv, rfl⟩]

/-- Bitmask mirror of `finiteBranchSearch`: `chosen` is the bitmask of the
chosen vertex set, the candidate vertices are bit indices, and an edge with
mask `m` is present exactly when `m &&& chosen = m`.

The inner loop is plain `Nat` bitwise arithmetic, so closed runs of this
search are cheap enough for kernel reduction. -/
def maskSearch (masks : List ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], need, chosen =>
      if masks.any (fun m => m &&& chosen == m) then false else decide (need = 0)
  | x :: xs, need, chosen =>
      if masks.any (fun m => m &&& chosen == m) then false
      else if need = 0 then true
      else if xs.length + 1 < need then false
      else maskSearch masks xs need chosen ||
        maskSearch masks xs (need - 1) (chosen ||| (1 <<< x))

/-- `maskSearch` computes `finiteBranchSearch` for the mask-based edge
detector, along the bitmask image of the search state. -/
theorem maskSearch_eq_finiteBranchSearch {V : Type*} [DecidableEq V]
    (masks : List ℕ) (toBit : V → ℕ) (xs : List V) (need : ℕ)
    (chosen : Finset V) :
    maskSearch masks (xs.map toBit) need (maskOfFn toBit chosen) =
      finiteBranchSearch
        (fun S => masks.any fun m => m &&& maskOfFn toBit S == m)
        xs need chosen := by
  induction xs generalizing need chosen with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, maskSearch, finiteBranchSearch,
        List.length_map, ← maskOfFn_insert, ih]

/-- Prefix-hitting from a closed bitmask search: if `maskSearch` finds no way
to choose `keep + 1` vertices from the prefix list `xs` while avoiding all
listed edge masks, then every subset of `P` larger than `keep` contains a
listed hyperedge. -/
theorem prefix_hitting_of_mask_search {V : Type*} [DecidableEq V]
    {badEdges : Finset (Finset V)} {toBit : V → ℕ}
    (htoBit : Function.Injective toBit)
    {edgeList : List (Finset V)}
    (hedges : ∀ E ∈ edgeList, E ∈ badEdges)
    {P : Finset V} {xs : List V} {keep : ℕ}
    (hxs : xs.toFinset = P)
    (hsearch : maskSearch (edgeList.map fun E => maskOfFn toBit E)
        (xs.map toBit) (keep + 1) 0 = false) :
    ∀ S : Finset V, S ⊆ P → keep < S.card → ContainsHyperedge badEdges S := by
  have hsound : ∀ S : Finset V,
      ((edgeList.map fun E => maskOfFn toBit E).any
        fun m => m &&& maskOfFn toBit S == m) = true →
      ContainsHyperedge badEdges S := by
    intro S hS
    rw [List.any_eq_true] at hS
    obtain ⟨m, hm, hmask⟩ := hS
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hm
    exact ⟨E, hedges E hE,
      (maskOfFn_land_eq_left_iff htoBit).mp (by simpa using hmask)⟩
  have hsearch' :
      finiteBranchSearch
        (fun S => (edgeList.map fun E => maskOfFn toBit E).any
          fun m => m &&& maskOfFn toBit S == m)
        xs (keep + 1) ∅ = false := by
    rw [← maskSearch_eq_finiteBranchSearch]
    simpa [maskOfFn_empty] using hsearch
  exact prefix_hitting_of_branch_search hsound hxs hsearch'

/-- The bitmask of a vertex *list* under the bit assignment `toBit`.

This is the `List`/`Nat`-only mirror of `maskOfFn`: it never builds a `Finset`,
so it is exactly the data that the closed bitmask search reduces over.  The
structural bridge `maskOfList_eq_maskOfFn_toFinset` connects it to the
`Finset`-based proof layer. -/
def maskOfList {V : Type*} (toBit : V → ℕ) (l : List V) : ℕ :=
  l.foldr (fun v acc => acc ||| 1 <<< toBit v) 0

@[simp] theorem maskOfList_nil {V : Type*} (toBit : V → ℕ) :
    maskOfList toBit ([] : List V) = 0 := rfl

theorem maskOfList_cons {V : Type*} (toBit : V → ℕ) (x : V) (l : List V) :
    maskOfList toBit (x :: l) = maskOfList toBit l ||| 1 <<< toBit x := rfl

/-- The list mask equals the `Finset` mask of the corresponding `toFinset`.

Purely structural (induction on the list, no `decide`): this is the key lemma
that keeps `Finset` entirely out of the compute path while still licensing the
`Finset`-based hitting proof. -/
theorem maskOfList_eq_maskOfFn_toFinset {V : Type*} [DecidableEq V]
    (toBit : V → ℕ) (l : List V) :
    maskOfList toBit l = maskOfFn toBit l.toFinset := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [maskOfList_cons, ih, List.toFinset_cons, maskOfFn_insert]

/-- Prefix-hitting from a closed bitmask search over *lists* of vertices.

Identical conclusion to `prefix_hitting_of_mask_search`, but the edges are
given as plain `List V` (with `toFinset` taken only in the proof layer) and the
search runs over `maskOfList`, so the closed boolean compiles with no `Finset`
in the compute path. -/
theorem prefix_hitting_of_mask_search_list {V : Type*} [DecidableEq V]
    {badEdges : Finset (Finset V)} {toBit : V → ℕ}
    (htoBit : Function.Injective toBit)
    {edgeLists : List (List V)}
    (hedges : ∀ l ∈ edgeLists, l.toFinset ∈ badEdges)
    {P : Finset V} {xs : List V} {keep : ℕ}
    (hxs : xs.toFinset = P)
    (hsearch : maskSearch (edgeLists.map (maskOfList toBit))
        (xs.map toBit) (keep + 1) 0 = false) :
    ∀ S : Finset V, S ⊆ P → keep < S.card → ContainsHyperedge badEdges S := by
  have hmap : edgeLists.map (maskOfList toBit) =
      (edgeLists.map (fun l => l.toFinset)).map (fun E => maskOfFn toBit E) := by
    rw [List.map_map]
    exact List.map_congr_left fun l _ => maskOfList_eq_maskOfFn_toFinset toBit l
  refine prefix_hitting_of_mask_search (badEdges := badEdges) (toBit := toBit)
    htoBit (edgeList := edgeLists.map (fun l => l.toFinset)) ?_ hxs ?_
  · intro E hE
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hE
    exact hedges l hl
  · rw [← hmap]; exact hsearch

/-- A replayable branch certificate for finite prefix hitting.

At an `edge E` leaf, the currently chosen vertices already contain the forbidden
edge `E`.  A `short` leaf says that fewer than `need` vertices remain, so no
completion of the required size exists.  A `branch` node skips or takes the next
available vertex. -/
inductive BranchCert (V : Type*) where
  | edge (E : Finset V)
  | short
  | branch (skip take : BranchCert V)

namespace BranchCert

variable {V : Type*} [DecidableEq V]

/-- Executable checker for a replayable branch certificate. -/
def check (badEdges : Finset (Finset V)) :
    BranchCert V → List V → ℕ → Finset V → Bool
  | edge E, _xs, _need, chosen => decide (E ∈ badEdges ∧ E ⊆ chosen)
  | short, xs, need, _chosen => decide (xs.length < need)
  | branch _ _, [], _need, _chosen => false
  | branch skip take, x :: xs, need, chosen =>
      if need = 0 then false
      else check badEdges skip xs need chosen &&
        check badEdges take xs (need - 1) (insert x chosen)

theorem check_complete {badEdges : Finset (Finset V)} :
    ∀ {cert : BranchCert V} {xs : List V} {need : ℕ} {chosen extra : Finset V},
      cert.check badEdges xs need chosen = true →
      extra ⊆ xs.toFinset →
      Disjoint chosen extra →
      extra.card = need →
      ContainsHyperedge badEdges (chosen ∪ extra)
  | edge E, _xs, _need, chosen, _extra, hcheck, _hextra, _hdisj, _hcard => by
      have h : E ∈ badEdges ∧ E ⊆ chosen := of_decide_eq_true hcheck
      exact containsHyperedge_mono Finset.subset_union_left ⟨E, h.1, h.2⟩
  | short, xs, need, _chosen, extra, hcheck, hextra, _hdisj, hcard => by
      have hshort : xs.length < need := of_decide_eq_true hcheck
      have hcard_le : extra.card ≤ xs.toFinset.card := Finset.card_le_card hextra
      have hto : xs.toFinset.card ≤ xs.length := List.toFinset_card_le xs
      omega
  | branch skip take, [], _need, _chosen, _extra, hcheck, _hextra, _hdisj, _hcard => by
      simp [check] at hcheck
  | branch skip take, x :: xs, need, chosen, extra, hcheck, hextra, hdisj, hcard => by
      by_cases hneed0 : need = 0
      · simp [check, hneed0] at hcheck
      · have hboth :
            skip.check badEdges xs need chosen = true ∧
              take.check badEdges xs (need - 1) (insert x chosen) = true := by
          have hand :
              (skip.check badEdges xs need chosen &&
                take.check badEdges xs (need - 1) (insert x chosen)) = true := by
            simpa [check, hneed0] using hcheck
          simpa using
            (Bool.and_eq_true_eq_eq_true_and_eq_true
              (skip.check badEdges xs need chosen)
              (take.check badEdges xs (need - 1) (insert x chosen))).mp hand
        by_cases hxextra : x ∈ extra
        · let extra' := extra.erase x
          have hsub : extra' ⊆ xs.toFinset := by
            intro y hy
            have hyextra : y ∈ extra := (Finset.mem_erase.mp hy).2
            have hyall := hextra hyextra
            simp only [List.toFinset_cons, Finset.mem_insert] at hyall
            rcases hyall with hyx | hyxs
            · have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
              exact (hyne hyx).elim
            · exact hyxs
          have hdisj' : Disjoint (insert x chosen) extra' := by
            rw [Finset.disjoint_left]
            intro y hyins hyextra'
            have hyextra : y ∈ extra := (Finset.mem_erase.mp hyextra').2
            simp only [Finset.mem_insert] at hyins
            rcases hyins with rfl | hychosen
            · exact (Finset.mem_erase.mp hyextra').1 rfl
            · exact (Finset.disjoint_left.mp hdisj hychosen) hyextra
          have hcard' : extra'.card = need - 1 := by
            rw [Finset.card_erase_of_mem hxextra]
            omega
          have hp' := check_complete hboth.2 hsub hdisj' hcard'
          have hunion : insert x chosen ∪ extra' = chosen ∪ extra := by
            ext y
            by_cases hyx : y = x
            · subst y
              simp [hxextra]
            · simp [extra', hyx, Finset.mem_erase]
          simpa [hunion] using hp'
        · have hsub : extra ⊆ xs.toFinset := by
            intro y hy
            have hyall := hextra hy
            simp only [List.toFinset_cons, Finset.mem_insert] at hyall
            rcases hyall with hyx | hyxs
            · subst y
              exact (hxextra hy).elim
            · exact hyxs
          exact check_complete hboth.1 hsub hdisj hcard

end BranchCert

theorem prefix_hitting_of_branch_certificate {V : Type*} [DecidableEq V]
    {badEdges : Finset (Finset V)} {cert : BranchCert V}
    {P : Finset V} {xs : List V} {keep : ℕ}
    (hxs : xs.toFinset = P)
    (hcheck : cert.check badEdges xs (keep + 1) ∅ = true) :
    ∀ S : Finset V, S ⊆ P → keep < S.card → ContainsHyperedge badEdges S := by
  intro S hS hcard
  obtain ⟨T, hTS, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := keep + 1) (Nat.succ_le_iff.mpr hcard)
  have hTlist : T ⊆ xs.toFinset := by
    rw [hxs]
    exact hTS.trans hS
  have hhit := BranchCert.check_complete
    (cert := cert) (xs := xs) (need := keep + 1) (chosen := ∅) (extra := T)
    hcheck hTlist (by simp) hTcard
  exact containsHyperedge_mono (by simpa using hTS) hhit

/-- A finite set of vertices hits every listed edge. -/
def IsVertexCover {V : Type*} [DecidableEq V] (edges : Finset (Finset V)) (C : Finset V) :
    Prop :=
  ∀ E ∈ edges, (E ∩ C).Nonempty

private theorem card_le_of_pairwise_disjoint_hits {V : Type*} [DecidableEq V]
    {edges : List (Finset V)} {C : Finset V}
    (hpair : edges.Pairwise Disjoint)
    (hhit : ∀ E ∈ edges, (E ∩ C).Nonempty) :
    edges.length ≤ C.card := by
  induction edges generalizing C with
  | nil =>
      simp
  | cons E edges ih =>
      cases hpair with
      | cons hdisj hpair_tail =>
          obtain ⟨x, hx⟩ := hhit E (by simp)
          have hxE : x ∈ E := (Finset.mem_inter.mp hx).1
          have hxC : x ∈ C := (Finset.mem_inter.mp hx).2
          have hhit_tail : ∀ F ∈ edges, (F ∩ C.erase x).Nonempty := by
            intro F hF
            obtain ⟨y, hy⟩ := hhit F (by simp [hF])
            have hyF : y ∈ F := (Finset.mem_inter.mp hy).1
            have hyC : y ∈ C := (Finset.mem_inter.mp hy).2
            have hyne : y ≠ x := by
              intro hEq
              subst y
              exact (Finset.disjoint_left.mp (hdisj F hF) hxE) hyF
            exact ⟨y, Finset.mem_inter.mpr ⟨hyF, Finset.mem_erase.mpr ⟨hyne, hyC⟩⟩⟩
          have htail := ih hpair_tail hhit_tail
          have hcard_erase : (C.erase x).card + 1 = C.card :=
            Finset.card_erase_add_one hxC
          simp only [List.length_cons]
          omega

/-- A compact certificate that every vertex cover has size at least a target.

A `disjoint` leaf closes the branch by listing pairwise-disjoint remaining edges.
A `branch` node names one remaining edge. Since a cover must contain a vertex of
that edge, every listed child proves the residual lower bound after selecting
one possible vertex. -/
inductive CoverLowerCert (V : Type*) where
  | disjoint (edges : List (Finset V))
  | branch (edge : Finset V) (children : List (V × CoverLowerCert V))

namespace CoverLowerCert

variable {V : Type*} [DecidableEq V]

/-- Compact DAG node used by generated certificates.  A finite amount of fuel
unfolds node references into an ordinary tree certificate. -/
inductive DagNode (V : Type*) where
  | disjoint (edges : List (Finset V))
  | branch (edge : Finset V) (children : List (V × ℕ))

/-- Unfold a compact DAG certificate into the replayable tree certificate.

The fuel parameter is a simple acyclicity guard for generated node tables.  The
checker for the resulting tree remains the trusted interface. -/
def ofDag (node : ℕ → DagNode V) : ℕ → ℕ → CoverLowerCert V
  | 0, _ => disjoint []
  | fuel + 1, root =>
      match node root with
      | DagNode.disjoint edges => disjoint edges
      | DagNode.branch edge children =>
          branch edge (children.map fun child => (child.1, ofDag node fuel child.2))

/-- Executable checker for vertex-cover lower-bound certificates. -/
def check (edges : Finset (Finset V)) : CoverLowerCert V → ℕ → Bool
  | _cert, 0 => true
  | disjoint witnesses, k + 1 =>
      decide (k + 1 ≤ witnesses.length) &&
        witnesses.all (fun E => decide (E ∈ edges ∧ E.Nonempty)) &&
        decide (witnesses.Pairwise Disjoint)
  | branch edge children, k + 1 =>
      decide (edge ∈ edges ∧ edge.Nonempty ∧
          edge ⊆ (children.map Prod.fst).toFinset) &&
        children.all
          (fun child =>
            decide (child.1 ∈ edge) &&
              check (edges.filter fun E => decide (child.1 ∉ E)) child.2 k)

theorem check_complete {edges : Finset (Finset V)} :
    ∀ {cert : CoverLowerCert V} {k : ℕ} {C : Finset V},
      cert.check edges k = true → IsVertexCover edges C → k ≤ C.card
  | _cert, 0, _C, _hcheck, _hcover => by simp
  | disjoint witnesses, k + 1, C, hcheck, hcover => by
      have hparts :
          (k + 1 ≤ witnesses.length) ∧
            (∀ E ∈ witnesses, E ∈ edges ∧ E.Nonempty) ∧
            witnesses.Pairwise Disjoint := by
        rw [check, Bool.and_eq_true_eq_eq_true_and_eq_true,
          Bool.and_eq_true_eq_eq_true_and_eq_true] at hcheck
        refine ⟨of_decide_eq_true hcheck.1.1, ?_, of_decide_eq_true hcheck.2⟩
        intro E hE
        have hall := (List.all_eq_true.mp hcheck.1.2) E hE
        exact of_decide_eq_true hall
      have hhit : ∀ E ∈ witnesses, (E ∩ C).Nonempty := by
        intro E hE
        exact hcover E (hparts.2.1 E hE).1
      have hlen := card_le_of_pairwise_disjoint_hits hparts.2.2 hhit
      omega
  | branch edge children, k + 1, C, hcheck, hcover => by
      rw [check, Bool.and_eq_true_eq_eq_true_and_eq_true] at hcheck
      have hedge :
          edge ∈ edges ∧ edge.Nonempty ∧ edge ⊆ (children.map Prod.fst).toFinset :=
        of_decide_eq_true hcheck.1
      obtain ⟨x, hx⟩ := hcover edge hedge.1
      have hxedge : x ∈ edge := (Finset.mem_inter.mp hx).1
      have hxC : x ∈ C := (Finset.mem_inter.mp hx).2
      have hxkeys : x ∈ (children.map Prod.fst).toFinset := hedge.2.2 hxedge
      rw [List.mem_toFinset] at hxkeys
      simp only [List.mem_map] at hxkeys
      rcases hxkeys with ⟨child, hchild_mem, hchild_fst⟩
      have hchild_all := (List.all_eq_true.mp hcheck.2) child hchild_mem
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hchild_all
      have hchild_check :
          child.2.check (edges.filter fun E => decide (x ∉ E)) k = true := by
        have hraw := hchild_all.2
        cases child with
        | mk v cert =>
            simp only at hchild_fst
            subst v
            exact hraw
      have hcover_child : IsVertexCover (edges.filter fun E => decide (x ∉ E)) (C.erase x) := by
        intro F hF
        have hFedges : F ∈ edges := (Finset.mem_filter.mp hF).1
        have hxnotF : x ∉ F := of_decide_eq_true (Finset.mem_filter.mp hF).2
        obtain ⟨y, hy⟩ := hcover F hFedges
        have hyF : y ∈ F := (Finset.mem_inter.mp hy).1
        have hyC : y ∈ C := (Finset.mem_inter.mp hy).2
        have hyne : y ≠ x := by
          intro hEq
          subst y
          exact hxnotF hyF
        exact ⟨y, Finset.mem_inter.mpr ⟨hyF, Finset.mem_erase.mpr ⟨hyne, hyC⟩⟩⟩
      have hrec := check_complete hchild_check hcover_child
      have hcard_erase : (C.erase x).card + 1 = C.card :=
        Finset.card_erase_add_one hxC
      omega

end CoverLowerCert

theorem prefix_hitting_of_cover_lower_certificate {V : Type*} [DecidableEq V]
    {badEdges : Finset (Finset V)} {cert : CoverLowerCert V}
    {P : Finset V} {keep lower : ℕ}
    (hPcard : P.card = keep + lower)
    (hcheck : cert.check (badEdges.filter fun E => decide (E ⊆ P)) lower = true) :
    ∀ S : Finset V, S ⊆ P → keep < S.card → ContainsHyperedge badEdges S := by
  intro S hS hcard
  by_contra hnot
  have hcover : IsVertexCover (badEdges.filter fun E => decide (E ⊆ P)) (P \ S) := by
    intro E hE
    have hEbad : E ∈ badEdges := (Finset.mem_filter.mp hE).1
    have hEP : E ⊆ P := of_decide_eq_true (Finset.mem_filter.mp hE).2
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hES : E ⊆ S := by
      intro x hxE
      by_contra hxS
      have hxDiff : x ∈ P \ S := Finset.mem_sdiff.mpr ⟨hEP hxE, hxS⟩
      have hxInter : x ∈ E ∩ (P \ S) := Finset.mem_inter.mpr ⟨hxE, hxDiff⟩
      rw [hempty] at hxInter
      simp at hxInter
    exact hnot ⟨E, hEbad, hES⟩
  have hlower := CoverLowerCert.check_complete hcheck hcover
  have hsdiff : (P \ S).card + S.card = P.card :=
    Finset.card_sdiff_add_card_eq_card hS
  omega

/-- A reciprocal identity edge over a multiplier map. The edge says that the
reciprocal of `target` is the sum of reciprocals over the nonempty right-hand
side `rhs`. -/
structure ReciprocalEdge {V : Type*} (mul : V → ℕ) where
  target : V
  rhs : Finset V
  target_not_rhs : target ∉ rhs
  rhs_nonempty : rhs.Nonempty
  identity : (1 / (mul target : ℚ)) = ∑ v ∈ rhs, (1 / (mul v : ℚ))

namespace ReciprocalEdge

variable {V : Type*} [DecidableEq V] {mul : V → ℕ}

/-- The finite support of a reciprocal edge. -/
def support (e : ReciprocalEdge mul) : Finset V :=
  insert e.target e.rhs

end ReciprocalEdge

/-- A generic scaled reciprocal obstruction. If the multiplier identity
`1/m_t = sum 1/m_r` holds and all scaled terms lie in a sum-free set, we get a
contradiction. -/
theorem scaled_reciprocal_identity_forbidden {V : Type*}
    {A : Finset ℕ} (hA : SumFree A) {mul : V → ℕ} {a : ℕ} (ha : 0 < a)
    (hmul_pos : ∀ v, 0 < mul v)
    (hmul_inj : Function.Injective fun v => mul v * a)
    {target : V} {rhs : Finset V}
    (htargetA : mul target * a ∈ A)
    (hrhsA : ∀ v ∈ rhs, mul v * a ∈ A)
    (htarget_not_rhs : target ∉ rhs) (hrhs_nonempty : rhs.Nonempty)
    (hid : (1 / (mul target : ℚ)) = ∑ v ∈ rhs, (1 / (mul v : ℚ))) : False := by
  let S : Finset ℕ := rhs.image fun v => mul v * a
  have hSsubset : S ⊆ A.erase (mul target * a) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    rw [Finset.mem_erase]
    exact ⟨fun hEq => by
      have hvt : v = target := hmul_inj hEq
      exact htarget_not_rhs (hvt ▸ hv), hrhsA v hv⟩
  have hSnonempty : S.Nonempty := by
    obtain ⟨v, hv⟩ := hrhs_nonempty
    exact ⟨mul v * a, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have hsum_image :
      (∑ b ∈ S, (1 / b : ℚ)) =
        ∑ v ∈ rhs, (1 / (mul v * a : ℕ) : ℚ) := by
    dsimp [S]
    rw [Finset.sum_image]
    intro v _ w _ hEq
    exact hmul_inj hEq
  have hscaled :
      (1 / (mul target * a : ℕ) : ℚ) =
        ∑ v ∈ rhs, (1 / (mul v * a : ℕ) : ℚ) := by
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have htargetQ : (mul target : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmul_pos target))
    have htarget_scale :
        (1 / (mul target * a : ℕ) : ℚ) =
          (1 / (a : ℚ)) * (1 / (mul target : ℚ)) := by
      push_cast
      field_simp [haQ, htargetQ]
    calc
      (1 / (mul target * a : ℕ) : ℚ)
          = (1 / (a : ℚ)) * (1 / (mul target : ℚ)) := htarget_scale
      _ = (1 / (a : ℚ)) * (∑ v ∈ rhs, (1 / (mul v : ℚ))) := by rw [hid]
      _ = ∑ v ∈ rhs, (1 / (a : ℚ)) * (1 / (mul v : ℚ)) := by
        rw [Finset.mul_sum]
      _ = ∑ v ∈ rhs, (1 / (mul v * a : ℕ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro v _
        have hvQ : (mul v : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmul_pos v))
        symm
        push_cast
        field_simp [haQ, hvQ]
  exact hA (mul target * a) htargetA S hSsubset hSnonempty
    (hscaled.trans hsum_image.symm)

/-- A reciprocal edge cannot be fully present in a scaled gadget inside a
sum-free set. -/
theorem reciprocalEdge_forbidden {V : Type*} [DecidableEq V]
    {A : Finset ℕ} (hA : SumFree A) {mul : V → ℕ} {a : ℕ} (ha : 0 < a)
    (hmul_pos : ∀ v, 0 < mul v)
    (hmul_inj : Function.Injective fun v => mul v * a)
    (e : ReciprocalEdge mul)
    (hEA : ∀ v ∈ e.support, mul v * a ∈ A) : False := by
  refine scaled_reciprocal_identity_forbidden hA ha hmul_pos hmul_inj
    (target := e.target) (rhs := e.rhs)
    (hEA e.target (Finset.mem_insert_self _ _)) ?_ e.target_not_rhs e.rhs_nonempty e.identity
  intro v hv
  exact hEA v (Finset.mem_insert_of_mem hv)

/-- Cast a denominator-cleared identity with common denominator `L` to a rational
reciprocal identity. This is the certificate format we want scripts to emit. -/
theorem reciprocal_identity_of_common_denominator {V : Type*}
    {mul : V → ℕ} {L : ℕ} (hLpos : 0 < L)
    (hmul_pos : ∀ v, 0 < mul v) (hmul_dvd : ∀ v, mul v ∣ L)
    {target : V} {rhs : Finset V}
    (hclear : L / mul target = ∑ v ∈ rhs, L / mul v) :
    (1 / (mul target : ℚ)) = ∑ v ∈ rhs, (1 / (mul v : ℚ)) := by
  have hdiv_cast : ∀ v : V, ((L / mul v : ℕ) : ℚ) = (L : ℚ) / (mul v : ℚ) := by
    intro v
    have hmQ : (mul v : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmul_pos v))
    have hmul_nat : mul v * (L / mul v) = L := Nat.mul_div_cancel' (hmul_dvd v)
    have hmul_q : (mul v : ℚ) * ((L / mul v : ℕ) : ℚ) = (L : ℚ) := by
      exact_mod_cast hmul_nat
    rw [eq_div_iff hmQ]
    simpa [mul_comm] using hmul_q
  have htarget : ((L / mul target : ℕ) : ℚ) = (L : ℚ) / (mul target : ℚ) :=
    hdiv_cast target
  have hrhs : ((∑ v ∈ rhs, L / mul v : ℕ) : ℚ) =
      ∑ v ∈ rhs, (L : ℚ) / (mul v : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun v _ => hdiv_cast v
  have hq : ((L / mul target : ℕ) : ℚ) =
      ((∑ v ∈ rhs, L / mul v : ℕ) : ℚ) := by
    exact_mod_cast hclear
  rw [htarget, hrhs] at hq
  have hLQ : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hLpos)
  have htQ : (mul target : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmul_pos target))
  calc
    (1 / (mul target : ℚ)) = ((L : ℚ) / (mul target : ℚ)) / L := by
      field_simp [hLQ, htQ]
    _ = (∑ v ∈ rhs, (L : ℚ) / (mul v : ℚ)) / L := by rw [hq]
    _ = ∑ v ∈ rhs, ((L : ℚ) / (mul v : ℚ)) / L := by
      rw [Finset.sum_div]
    _ = ∑ v ∈ rhs, (1 / (mul v : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      have hvQ : (mul v : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmul_pos v))
      field_simp [hLQ, hvQ]

end UnitFractionSets
