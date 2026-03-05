/-
# Structural results for PairFree sets

The key result: (n, c·n) is a unit fraction pair iff (c+1) ∣ n.
This gives an infinite family of forbidden pair constraints for PairFree sets.
-/
import Erdos.UnitFractionPairs.Classification
import Erdos.Common.PackingBound

namespace UnitFractionPairs

/-! ## General multiple characterization -/

/-- For any c ≥ 1 and n ≥ 1, (n, c·n) is a unit fraction pair iff (c+1) ∣ n.

    Proof: n + cn = (c+1)n and n · cn = cn². So (c+1)n ∣ cn²
    iff (c+1) ∣ cn iff (c+1) ∣ n (since gcd(c, c+1) = 1). -/
theorem pair_n_cn_iff {n c : ℕ} (hn : 0 < n) (_hc : 0 < c) :
    IsUnitFractionPair n (c * n) ↔ (c + 1) ∣ n := by
  unfold IsUnitFractionPair
  constructor
  · intro ⟨k, hk⟩
    have h2 : n + c * n = (c + 1) * n := by ring
    rw [h2] at hk
    -- hk : n * (c * n) = (c + 1) * n * k
    have h3 : n * (c * n) = n * ((c + 1) * k) := by linarith
    have h4 : c * n = (c + 1) * k :=
      Nat.eq_of_mul_eq_mul_left hn h3
    have h5 : (c + 1) ∣ c * n := ⟨k, h4⟩
    have hcop : Nat.Coprime (c + 1) c := by
      rw [show c + 1 = c + 1 from rfl, Nat.coprime_self_add_left]
      exact Nat.coprime_one_left c
    exact hcop.dvd_of_dvd_mul_left h5
  · intro ⟨k, hk⟩
    subst hk
    exact ⟨c * k, by ring⟩

/-! ## Special cases -/

/-- (n, 2n) is a unit fraction pair iff 3 ∣ n. -/
theorem pair_n_2n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair n (2 * n) ↔ 3 ∣ n :=
  pair_n_cn_iff hn (by omega)

/-- (n, 3n) is a unit fraction pair iff 4 ∣ n. -/
theorem pair_n_3n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair n (3 * n) ↔ 4 ∣ n :=
  pair_n_cn_iff hn (by omega)

/-- (n, 4n) is a unit fraction pair iff 5 ∣ n. -/
theorem pair_n_4n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair n (4 * n) ↔ 5 ∣ n :=
  pair_n_cn_iff hn (by omega)

/-- (2n, 3n) is a unit fraction pair iff 5 ∣ n.

    This is the multiplier triangle edge (2,3) from gadget mining:
    2n + 3n = 5n divides (2n)(3n) = 6n² iff 5 divides n. -/
theorem pair_2n_3n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair (2 * n) (3 * n) ↔ 5 ∣ n := by
  unfold IsUnitFractionPair
  constructor
  · intro ⟨k, hk⟩
    have hEq : 6 * n * n = 5 * n * k := by
      calc
        6 * n * n = (2 * n) * (3 * n) := by ring
        _ = (2 * n + 3 * n) * k := hk
        _ = 5 * n * k := by ring
    have hEq' : n * (6 * n) = n * (5 * k) := by nlinarith [hEq]
    have hEq'' : 6 * n = 5 * k := Nat.eq_of_mul_eq_mul_left hn hEq'
    have h5dvd6n : 5 ∣ 6 * n := ⟨k, hEq''⟩
    exact (by decide : Nat.Coprime 5 6).dvd_of_dvd_mul_left h5dvd6n
  · rintro ⟨m, rfl⟩
    exact ⟨6 * m, by ring⟩

/-! ## Constraints on PairFree sets -/

/-- Symmetry: IsUnitFractionPair is symmetric. -/
theorem pair_symm {a b : ℕ} : IsUnitFractionPair a b ↔ IsUnitFractionPair b a := by
  unfold IsUnitFractionPair
  constructor <;> intro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩

/-- If n and 2n are both in a PairFree set, then 3 ∤ n. -/
theorem pair_free_double_not_div3 {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (hn_mem : n ∈ A) (h2n_mem : 2 * n ∈ A) :
    ¬(3 ∣ n) := by
  intro hdvd
  exact hA n hn_mem (2 * n) h2n_mem (by omega) ((pair_n_2n_iff hn).mpr hdvd)

/-- If n and 3n are both in a PairFree set, then 4 ∤ n. -/
theorem pair_free_triple_not_div4 {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (hn_mem : n ∈ A) (h3n_mem : 3 * n ∈ A) :
    ¬(4 ∣ n) := by
  intro hdvd
  exact hA n hn_mem (3 * n) h3n_mem (by omega) ((pair_n_3n_iff hn).mpr hdvd)

/-- If 2n and 3n are both in a PairFree set, then 5 ∤ n.

    This is the third edge in the multiplier triangle {1,2,3}. -/
theorem pair_free_double_triple_not_div5 {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (h2n_mem : 2 * n ∈ A) (h3n_mem : 3 * n ∈ A) :
    ¬(5 ∣ n) := by
  intro hdvd
  exact hA (2 * n) h2n_mem (3 * n) h3n_mem (by omega) ((pair_2n_3n_iff hn).mpr hdvd)

/-- If n, 2n, 3n all lie in a PairFree set, then n avoids all triangle divisibility
    triggers 3, 4, and 5. -/
theorem pair_free_n_2n_3n_constraints {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (hn_mem : n ∈ A) (h2n_mem : 2 * n ∈ A) (h3n_mem : 3 * n ∈ A) :
    ¬(3 ∣ n) ∧ ¬(4 ∣ n) ∧ ¬(5 ∣ n) := by
  refine ⟨pair_free_double_not_div3 hA hn hn_mem h2n_mem, ?_, ?_⟩
  · exact pair_free_triple_not_div4 hA hn hn_mem h3n_mem
  · exact pair_free_double_triple_not_div5 hA hn h2n_mem h3n_mem

/-- If `60 ∣ n`, all three edges of the multiplier triangle `{n, 2n, 3n}` are
    unit-fraction pairs. -/
theorem triangle_pairs_of_dvd60 {n : ℕ} (hn : 0 < n) (h60 : 60 ∣ n) :
    IsUnitFractionPair n (2 * n) ∧
    IsUnitFractionPair n (3 * n) ∧
    IsUnitFractionPair (2 * n) (3 * n) := by
  have h3 : 3 ∣ n := dvd_trans (by decide : 3 ∣ 60) h60
  have h4 : 4 ∣ n := dvd_trans (by decide : 4 ∣ 60) h60
  have h5 : 5 ∣ n := dvd_trans (by decide : 5 ∣ 60) h60
  exact ⟨(pair_n_2n_iff hn).mpr h3, (pair_n_3n_iff hn).mpr h4, (pair_2n_3n_iff hn).mpr h5⟩

/-- Any two distinct elements chosen from `{n, 2n, 3n}` form a unit-fraction pair
    whenever `60 ∣ n`. -/
private theorem triangle_mem_pair {n x y : ℕ} (hn : 0 < n) (h60 : 60 ∣ n)
    (hx : x ∈ ({n, 2 * n, 3 * n} : Finset ℕ))
    (hy : y ∈ ({n, 2 * n, 3 * n} : Finset ℕ)) (hxy : x ≠ y) :
    IsUnitFractionPair x y := by
  rcases triangle_pairs_of_dvd60 hn h60 with ⟨h12, h13, h23⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl
    · exact False.elim (hxy rfl)
    · exact h12
    · exact h13
  · rcases hy with rfl | rfl | rfl
    · exact (pair_symm).2 h12
    · exact False.elim (hxy rfl)
    · exact h23
  · rcases hy with rfl | rfl | rfl
    · exact (pair_symm).2 h13
    · exact (pair_symm).2 h23
    · exact False.elim (hxy rfl)

/-- **Triangle gadget forcing (`τ = 2`).**

    In a pair-free set, when `60 ∣ n`, the intersection with `{n, 2n, 3n}`
    has cardinality at most 1 (so at least 2 elements of the triangle are excluded). -/
theorem pair_free_triangle_inter_card_le_one {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (h60 : 60 ∣ n) :
    (({n, 2 * n, 3 * n} : Finset ℕ) ∩ A).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  by_contra hxy
  have hxG : x ∈ ({n, 2 * n, 3 * n} : Finset ℕ) := (Finset.mem_inter.mp hx).1
  have hyG : y ∈ ({n, 2 * n, 3 * n} : Finset ℕ) := (Finset.mem_inter.mp hy).1
  have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
  have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
  have hpair : IsUnitFractionPair x y := triangle_mem_pair hn h60 hxG hyG hxy
  exact (hA x hxA y hyA hxy hpair).elim

/-- The multiplier triangle `{n, 2n, 3n}` has cardinality exactly 3 for `n > 0`. -/
theorem triangle_card_eq_three {n : ℕ} (hn : 0 < n) :
    ({n, 2 * n, 3 * n} : Finset ℕ).card = 3 := by
  have h12 : n ≠ 2 * n := by omega
  have h13 : n ≠ 3 * n := by omega
  have h23 : 2 * n ≠ 3 * n := by omega
  rw [show ({n, 2 * n, 3 * n} : Finset ℕ) =
      insert n (insert (2 * n) ({3 * n} : Finset ℕ)) by rfl]
  rw [Finset.card_insert_of_notMem (by simp [h12, h13])]
  rw [Finset.card_insert_of_notMem (by simp [h23])]
  simp

/-- Under `60 ∣ n`, a pair-free set omits at least two elements from `{n, 2n, 3n}`. -/
theorem pair_free_triangle_omits_at_least_two {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (h60 : 60 ∣ n) :
    ({n, 2 * n, 3 * n} : Finset ℕ).card - (({n, 2 * n, 3 * n} : Finset ℕ) ∩ A).card ≥ 2 := by
  have hcard : ({n, 2 * n, 3 * n} : Finset ℕ).card = 3 := triangle_card_eq_three hn
  have hinter : (({n, 2 * n, 3 * n} : Finset ℕ) ∩ A).card ≤ 1 :=
    pair_free_triangle_inter_card_le_one hA hn h60
  omega

/-! ## Disjoint triangle-family packing -/

/-- If `d` is coprime to `6`, then `2 ∤ d`. -/
private theorem not_dvd_two_of_coprime6 {d : ℕ} (hd : Nat.Coprime d 6) : ¬(2 ∣ d) := by
  intro h2
  exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hd

/-- If `d` is coprime to `6`, then `3 ∤ d`. -/
private theorem not_dvd_three_of_coprime6 {d : ℕ} (hd : Nat.Coprime d 6) : ¬(3 ∣ d) := by
  intro h3
  exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hd

/-- Triangle gadgets `{60d,120d,180d}` are pairwise disjoint for distinct
    coprime-to-6 parameters. -/
theorem triangles_disjoint_coprime6 {d₁ d₂ : ℕ} (hne : d₁ ≠ d₂)
    (h1 : Nat.Coprime d₁ 6) (h2 : Nat.Coprime d₂ 6) :
    Disjoint ({60 * d₁, 120 * d₁, 180 * d₁} : Finset ℕ) {60 * d₂, 120 * d₂, 180 * d₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with rfl | rfl | rfl <;> rcases hx₂ with h | h | h
  · exact hne (by omega)
  · exact not_dvd_two_of_coprime6 h1 ⟨d₂, by omega⟩
  · exact not_dvd_three_of_coprime6 h1 ⟨d₂, by omega⟩
  · exact not_dvd_two_of_coprime6 h2 ⟨d₁, by omega⟩
  · exact hne (by omega)
  · have h23d : 2 * d₁ = 3 * d₂ := by omega
    have h2d : 2 ∣ 3 * d₂ := ⟨d₁, h23d.symm⟩
    exact not_dvd_two_of_coprime6 h2
      (((Nat.Prime.dvd_mul Nat.prime_two).mp h2d).resolve_left (by decide))
  · exact not_dvd_three_of_coprime6 h2 ⟨d₁, by omega⟩
  · have h32d : 3 * d₁ = 2 * d₂ := by omega
    have h2d : 2 ∣ 3 * d₁ := ⟨d₂, h32d⟩
    exact not_dvd_two_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_two).mp h2d).resolve_left (by decide))
  · exact hne (by omega)

/-- **Global bound from disjoint triangle gadgets.**

    Let `D = { d ∈ [1, N/180] : Nat.Coprime d 6 }` and gadget
    `T_d = {60d, 120d, 180d}`. For pair-free `A ⊆ [1,N]`, each `T_d`
    contributes at least two omissions, so:

    `A.card + 2 * |D| ≤ N`. -/
theorem pair_free_triangle_family_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card ≤ N := by
  set D := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) with hD_def
  let triangle : ℕ → Finset ℕ := fun d => {60 * d, 120 * d, 180 * d}
  have hD_mem : ∀ d ∈ D, 0 < d ∧ Nat.Coprime d 6 ∧ 180 * d ≤ N := by
    intro d hd
    simp only [hD_def, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  have h := PackingBound.single_family_bound N A D triangle 3 1
    (by omega) hAN
    (fun d₁ hd₁ d₂ hd₂ hne =>
      triangles_disjoint_coprime6 hne
        (hD_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
        (hD_mem d₂ (Finset.mem_coe.mp hd₂)).2.1)
    (fun d hd => by
      have hdpos : 0 < d := (hD_mem d hd).1
      have h60d_pos : 0 < 60 * d := by omega
      simpa [triangle, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using triangle_card_eq_three h60d_pos)
    (fun d hd => by
      have hdpos : 0 < d := (hD_mem d hd).1
      have h60d_pos : 0 < 60 * d := by omega
      have h60div : 60 ∣ 60 * d := ⟨d, by ring⟩
      simpa [triangle, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using pair_free_triangle_inter_card_le_one hA h60d_pos h60div)
    (Finset.biUnion_subset.mpr fun d hd => by
      have hdpos : 0 < d := (hD_mem d hd).1
      have hN : 180 * d ≤ N := (hD_mem d hd).2.2
      intro x hx
      simp only [triangle, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      rcases hx with rfl | rfl | rfl
      · refine ⟨by omega, ?_⟩
        exact le_trans (by nlinarith : 60 * d ≤ 180 * d) hN
      · refine ⟨by omega, ?_⟩
        exact le_trans (by nlinarith : 120 * d ≤ 180 * d) hN
      · exact ⟨by omega, hN⟩)
  omega

/-- Master constraint: a PairFree set that contains both n and c·n
    (with c ≥ 2) cannot have (c+1) ∣ n. -/
theorem pair_free_cn_constraint {A : Finset ℕ} (hA : PairFree A)
    {n c : ℕ} (hn : 0 < n) (hc : 1 < c) (hn_mem : n ∈ A)
    (hcn_mem : c * n ∈ A) : ¬((c + 1) ∣ n) := by
  intro hdvd
  have hne : n ≠ c * n := by nlinarith
  exact hA n hn_mem (c * n) hcn_mem hne ((pair_n_cn_iff hn (by omega)).mpr hdvd)

end UnitFractionPairs
