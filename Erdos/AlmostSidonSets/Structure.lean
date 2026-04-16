/- 
# Structural Decomposition Around an Exceptional Sum

If every repeated two-sum of `A` is forced to equal `n`, then the lower half
`A ∩ [1, ⌊n/2⌋]` and the upper half `A ∩ [⌊n/2⌋+1, ∞)` are each genuine Sidon
sets. This gives a clean first structural reduction for upper-bound arguments.
-/
import Erdos.AlmostSidonSets.Statement

namespace AlmostSidonSets

/-- All repeated two-sums of `A` are concentrated at the value `n`. -/
def ExceptionalAt (A : Finset ℕ) (n : ℕ) : Prop :=
  ∀ m : ℕ, HasTwoSumReprs A m → m = n

/-- The part of `A` at or below the midpoint `n / 2`. -/
def lowerPart (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a => 2 * a ≤ n

/-- The part of `A` strictly above the midpoint `n / 2`. -/
def upperPart (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a => n < 2 * a

@[simp] theorem mem_lowerPart {n : ℕ} {A : Finset ℕ} {a : ℕ} :
    a ∈ lowerPart n A ↔ a ∈ A ∧ 2 * a ≤ n := by
  simp [lowerPart]

@[simp] theorem mem_upperPart {n : ℕ} {A : Finset ℕ} {a : ℕ} :
    a ∈ upperPart n A ↔ a ∈ A ∧ n < 2 * a := by
  simp [upperPart]

/-- A witnessed repeated sum in an almost-Sidon set determines the exceptional
value. -/
theorem exceptionalAt_of_hasTwoSumReprs {A : Finset ℕ} {n : ℕ}
    (hA : AlmostSidonFinset A) (hn : HasTwoSumReprs A n) :
    ExceptionalAt A n := by
  intro m hm
  exact hA m n hm hn

/-- The lower half of an almost-Sidon set is genuinely Sidon. -/
theorem exceptionalAt_lowerPart_isSidon {A : Finset ℕ} {n : ℕ}
    (hExc : ExceptionalAt A n) :
    IsSidonFinset (lowerPart n A) := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha12 hb12 hsum
  have ha₁' := mem_lowerPart.mp (Finset.mem_coe.mp ha₁)
  have ha₂' := mem_lowerPart.mp (Finset.mem_coe.mp ha₂)
  have hb₁' := mem_lowerPart.mp (Finset.mem_coe.mp hb₁)
  have hb₂' := mem_lowerPart.mp (Finset.mem_coe.mp hb₂)
  by_cases hsame : a₁ = b₁ ∧ a₂ = b₂
  · exact hsame
  · have hneq : a₁ ≠ b₁ ∨ a₂ ≠ b₂ := by
      by_cases h1 : a₁ = b₁
      · right
        intro h2
        exact hsame ⟨h1, h2⟩
      · exact Or.inl h1
    have hrepr : HasTwoSumReprs A (a₁ + a₂) := by
      exact ⟨a₁, ha₁'.1, a₂, ha₂'.1, b₁, hb₁'.1, b₂, hb₂'.1,
        ha12, hb12, rfl, hsum.symm, hneq⟩
    have hcenter : a₁ + a₂ = n := hExc _ hrepr
    have haeq : a₁ = a₂ := by
      omega
    have hbeq : b₁ = b₂ := by
      omega
    subst haeq
    subst hbeq
    omega

/-- The upper half of an almost-Sidon set is genuinely Sidon. -/
theorem exceptionalAt_upperPart_isSidon {A : Finset ℕ} {n : ℕ}
    (hExc : ExceptionalAt A n) :
    IsSidonFinset (upperPart n A) := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha12 hb12 hsum
  have ha₁' := mem_upperPart.mp (Finset.mem_coe.mp ha₁)
  have ha₂' := mem_upperPart.mp (Finset.mem_coe.mp ha₂)
  have hb₁' := mem_upperPart.mp (Finset.mem_coe.mp hb₁)
  have hb₂' := mem_upperPart.mp (Finset.mem_coe.mp hb₂)
  by_cases hsame : a₁ = b₁ ∧ a₂ = b₂
  · exact hsame
  · have hneq : a₁ ≠ b₁ ∨ a₂ ≠ b₂ := by
      by_cases h1 : a₁ = b₁
      · right
        intro h2
        exact hsame ⟨h1, h2⟩
      · exact Or.inl h1
    have hrepr : HasTwoSumReprs A (a₁ + a₂) := by
      exact ⟨a₁, ha₁'.1, a₂, ha₂'.1, b₁, hb₁'.1, b₂, hb₂'.1,
        ha12, hb12, rfl, hsum.symm, hneq⟩
    have hcenter : a₁ + a₂ = n := hExc _ hrepr
    have hgt : n < a₁ + a₂ := by
      omega
    omega

/-- The midpoint split partitions `A`. -/
theorem lowerPart_union_upperPart (n : ℕ) (A : Finset ℕ) :
    lowerPart n A ∪ upperPart n A = A := by
  ext a
  by_cases h : 2 * a ≤ n
  · simp [lowerPart, upperPart, h]
  · simp [lowerPart, upperPart, h, Nat.lt_of_not_ge h]

/-- The midpoint split is disjoint. -/
theorem disjoint_lowerPart_upperPart (n : ℕ) (A : Finset ℕ) :
    Disjoint (lowerPart n A) (upperPart n A) := by
  refine Finset.disjoint_left.mpr ?_
  intro a haL haU
  have haL' := mem_lowerPart.mp haL
  have haU' := mem_upperPart.mp haU
  omega

/-- Therefore the midpoint split gives an exact cardinality decomposition. -/
theorem card_lowerPart_add_card_upperPart (n : ℕ) (A : Finset ℕ) :
    (lowerPart n A).card + (upperPart n A).card = A.card := by
  have hdisj : Disjoint (lowerPart n A) (upperPart n A) :=
    disjoint_lowerPart_upperPart n A
  have hunion : lowerPart n A ∪ upperPart n A = A :=
    lowerPart_union_upperPart n A
  symm
  simpa [hunion, Nat.add_comm] using Finset.card_union_of_disjoint hdisj

end AlmostSidonSets
