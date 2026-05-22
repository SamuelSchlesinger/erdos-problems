import Erdos.SumProduct.Statement

/-
# Elementary facts for Erdos Problem 52

This file records the first sanity checks for the finite sum-product model:
empty and singleton sets, membership introduction for `A + A` and `A * A`, and
the elementary injection showing that a nonempty finite set injects into its
sumset by translation.
-/
namespace SumProduct

/-- The empty set has empty sumset. -/
@[simp] theorem sumset_empty :
    sumset (∅ : Finset Int) = ∅ := by
  simp [sumset]

/-- The empty set has empty product set. -/
@[simp] theorem productSet_empty :
    productSet (∅ : Finset Int) = ∅ := by
  simp [productSet]

/-- The sum-product maximum for the empty set is zero. -/
@[simp] theorem sumProductMax_empty :
    sumProductMax (∅ : Finset Int) = 0 := by
  simp [sumProductMax]

/-- The sumset of a singleton is the singleton containing the doubled element. -/
@[simp] theorem sumset_singleton (a : Int) :
    sumset ({a} : Finset Int) = {a + a} := by
  simp [sumset]

/-- The product set of a singleton is the singleton containing the square. -/
@[simp] theorem productSet_singleton (a : Int) :
    productSet ({a} : Finset Int) = {a * a} := by
  simp [productSet]

/-- A singleton has sumset of cardinality one. -/
@[simp] theorem sumset_singleton_card (a : Int) :
    (sumset ({a} : Finset Int)).card = 1 := by
  simp

/-- A singleton has product set of cardinality one. -/
@[simp] theorem productSet_singleton_card (a : Int) :
    (productSet ({a} : Finset Int)).card = 1 := by
  simp

/-- The sum-product maximum of a singleton is one. -/
@[simp] theorem sumProductMax_singleton (a : Int) :
    sumProductMax ({a} : Finset Int) = 1 := by
  simp [sumProductMax]

/-- If `a` and `b` lie in `A`, then their sum lies in `A + A`. -/
theorem mem_sumset_of_mem {A : Finset Int} {a b : Int}
    (ha : a ∈ A) (hb : b ∈ A) :
    a + b ∈ sumset A := by
  exact Finset.mem_image.mpr ⟨(a, b), by simp [ha, hb], rfl⟩

/-- If `a` and `b` lie in `A`, then their product lies in `A * A`. -/
theorem mem_productSet_of_mem {A : Finset Int} {a b : Int}
    (ha : a ∈ A) (hb : b ∈ A) :
    a * b ∈ productSet A := by
  exact Finset.mem_image.mpr ⟨(a, b), by simp [ha, hb], rfl⟩

/-- Membership in the sumset is exactly representation as `a + b` with
`a, b ∈ A`. -/
theorem mem_sumset {A : Finset Int} {n : Int} :
    n ∈ sumset A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, hpval⟩
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    exact ⟨p.1, ha, p.2, hb, hpval⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mem_sumset_of_mem ha hb

/-- Membership in the product set is exactly representation as `a * b` with
`a, b ∈ A`. -/
theorem mem_productSet {A : Finset Int} {n : Int} :
    n ∈ productSet A ↔ ∃ a ∈ A, ∃ b ∈ A, a * b = n := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, hpval⟩
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    exact ⟨p.1, ha, p.2, hb, hpval⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mem_productSet_of_mem ha hb

/-- A nonempty finite set injects into its sumset by translating by any fixed
element of the set. Thus `|A| <= |A + A|` for nonempty `A`. -/
theorem card_le_sumset_card_of_nonempty {A : Finset Int} (hA : A.Nonempty) :
    A.card ≤ (sumset A).card := by
  rcases hA with ⟨x, hx⟩
  let translate : Int → Int := fun a => a + x
  have hsubset : A.image translate ⊆ sumset A := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    exact mem_sumset_of_mem ha hx
  have hcard_image : (A.image translate).card = A.card := by
    rw [Finset.card_image_of_injOn]
    intro a _ b _ h
    exact add_right_cancel h
  rw [← hcard_image]
  exact Finset.card_le_card hsubset

/-- The sum-product maximum is at least `|A|` for every nonempty finite set,
already because the sumset has size at least `|A|`. -/
theorem card_le_sumProductMax_of_nonempty {A : Finset Int} (hA : A.Nonempty) :
    A.card ≤ sumProductMax A := by
  exact le_trans (card_le_sumset_card_of_nonempty hA)
    (Nat.le_max_left (sumset A).card (productSet A).card)

end SumProduct
