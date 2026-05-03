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
