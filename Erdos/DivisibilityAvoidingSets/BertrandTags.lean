import Erdos.DivisibilityAvoidingSets.TaggedAP
import Mathlib.NumberTheory.Bertrand

/-!
# Bertrand prime tags for Erdős problem #12

The tagged block criterion needs pairwise-coprime tags that grow slowly enough
for a dense block construction.  We use Bertrand's postulate recursively:
start at `3`, and choose the next prime in `(q, 2q]`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false
set_option linter.style.longLine false

/-- Auxiliary subtype-valued version of the Bertrand prime tags. -/
noncomputable def oddPrimeTagAux : ℕ → {p : ℕ // Nat.Prime p}
  | 0 => ⟨3, Nat.prime_three⟩
  | n + 1 =>
      let prev := oddPrimeTagAux n
      let ex := Nat.exists_prime_lt_and_le_two_mul prev.1 prev.2.ne_zero
      ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩

/-- A concrete increasing sequence of odd prime tags. -/
noncomputable def oddPrimeTag (n : ℕ) : ℕ :=
  (oddPrimeTagAux n).1

theorem oddPrimeTag_prime (n : ℕ) :
    Nat.Prime (oddPrimeTag n) :=
  (oddPrimeTagAux n).2

theorem oddPrimeTag_lt_succ (n : ℕ) :
    oddPrimeTag n < oddPrimeTag (n + 1) := by
  let ex :=
    Nat.exists_prime_lt_and_le_two_mul
      (oddPrimeTagAux n).1 (oddPrimeTagAux n).2.ne_zero
  change (oddPrimeTagAux n).1 < Classical.choose ex
  exact (Classical.choose_spec ex).2.1

theorem oddPrimeTag_succ_le_two_mul (n : ℕ) :
    oddPrimeTag (n + 1) ≤ 2 * oddPrimeTag n := by
  let ex :=
    Nat.exists_prime_lt_and_le_two_mul
      (oddPrimeTagAux n).1 (oddPrimeTagAux n).2.ne_zero
  change Classical.choose ex ≤ 2 * (oddPrimeTagAux n).1
  exact (Classical.choose_spec ex).2.2

theorem oddPrimeTag_strictMono :
    StrictMono oddPrimeTag :=
  strictMono_nat_of_lt_succ oddPrimeTag_lt_succ

theorem oddPrimeTag_mono :
    Monotone oddPrimeTag :=
  oddPrimeTag_strictMono.monotone

theorem oddPrimeTag_injective :
    Function.Injective oddPrimeTag :=
  oddPrimeTag_strictMono.injective

theorem oddPrimeTag_nonzero (i : ℕ) :
    oddPrimeTag i ≠ 0 :=
  (oddPrimeTag_prime i).ne_zero

theorem oddPrimeTag_pos (i : ℕ) :
    0 < oddPrimeTag i :=
  (oddPrimeTag_prime i).pos

theorem oddPrimeTag_two_lt (i : ℕ) :
    2 < oddPrimeTag i := by
  have h0 : oddPrimeTag 0 = 3 := rfl
  have hle : oddPrimeTag 0 ≤ oddPrimeTag i :=
    oddPrimeTag_mono (Nat.zero_le i)
  omega

theorem oddPrimeTag_coprime_of_ne {i j : ℕ} (hij : i ≠ j) :
    Nat.Coprime (oddPrimeTag i) (oddPrimeTag j) := by
  refine (Nat.coprime_primes (oddPrimeTag_prime i) (oddPrimeTag_prime j)).mpr ?_
  exact fun h => hij (oddPrimeTag_injective h)

theorem oddPrimeTag_pairwise_on_range (i : ℕ) :
    Set.Pairwise (Finset.range (i + 1))
      (fun a b => Nat.Coprime (oddPrimeTag a) (oddPrimeTag b)) := by
  intro a _ha b _hb hab
  exact oddPrimeTag_coprime_of_ne hab

theorem oddPrimeTag_not_dvd_one (i : ℕ) :
    ¬ oddPrimeTag i ∣ 1 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 1) h
  have hlt := oddPrimeTag_two_lt i
  omega

theorem oddPrimeTag_not_dvd_two (i : ℕ) :
    ¬ oddPrimeTag i ∣ 2 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 2) h
  have hlt := oddPrimeTag_two_lt i
  omega

/-- The modulus used for block `i`: the product of tags up to and including
`i`. -/
noncomputable def tagModulus (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (i + 1), oddPrimeTag j

theorem tagModulus_pos (i : ℕ) :
    0 < tagModulus i := by
  unfold tagModulus
  exact Finset.prod_pos fun j _ => oddPrimeTag_pos j

theorem oddPrimeTag_dvd_tagModulus_of_le {j i : ℕ} (hji : j ≤ i) :
    oddPrimeTag j ∣ tagModulus i := by
  unfold tagModulus
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hji))

/-- Residues for block `i`: `0` at its own tag, `1` at all earlier tags. -/
def tagResidueTarget (i j : ℕ) : ℕ :=
  if j = i then 0 else 1

/-- CRT residue for block `i`, modulo `tagModulus i`. -/
noncomputable def tagResidue (i : ℕ) : ℕ :=
  (Nat.chineseRemainderOfFinset
    (tagResidueTarget i) oddPrimeTag (Finset.range (i + 1))
    (fun j _ => oddPrimeTag_nonzero j) (oddPrimeTag_pairwise_on_range i)).1

theorem tagResidue_modEq_of_le {i j : ℕ} (hji : j ≤ i) :
    tagResidue i ≡ tagResidueTarget i j [MOD oddPrimeTag j] := by
  unfold tagResidue
  exact
    (Nat.chineseRemainderOfFinset
      (tagResidueTarget i) oddPrimeTag (Finset.range (i + 1))
      (fun j _ => oddPrimeTag_nonzero j) (oddPrimeTag_pairwise_on_range i)).2
      j (Finset.mem_range.mpr (Nat.lt_succ_of_le hji))

theorem tagResidue_modEq_zero (i : ℕ) :
    tagResidue i ≡ 0 [MOD oddPrimeTag i] := by
  simpa [tagResidueTarget] using
    tagResidue_modEq_of_le (i := i) (j := i) le_rfl

theorem tagResidue_modEq_one_of_lt {j i : ℕ} (hji : j < i) :
    tagResidue i ≡ 1 [MOD oddPrimeTag j] := by
  have hle : j ≤ i := hji.le
  have hne : j ≠ i := Nat.ne_of_lt hji
  simpa [tagResidueTarget, hne] using
    tagResidue_modEq_of_le (i := i) (j := j) hle

theorem tagResidue_lt_tagModulus (i : ℕ) :
    tagResidue i < tagModulus i := by
  unfold tagResidue tagModulus
  exact Nat.chineseRemainderOfFinset_lt_prod
    (tagResidueTarget i) oddPrimeTag
    (fun j _ => oddPrimeTag_nonzero j) (oddPrimeTag_pairwise_on_range i)

theorem oddPrimeTag_dvd_of_mem_taggedBlock {T L : ℕ → ℕ} {i x : ℕ}
    (hx : x ∈ apBlock (tagResidue i) (tagModulus i) (T i) (L i)) :
    oddPrimeTag i ∣ x := by
  have hmod : x ≡ 0 [MOD oddPrimeTag i] :=
    modEq_of_mem_apBlock
      (oddPrimeTag_dvd_tagModulus_of_le (j := i) (i := i) le_rfl)
      (tagResidue_modEq_zero i) hx
  exact Nat.modEq_zero_iff_dvd.mp hmod

theorem taggedBlock_modEq_one_of_lt {T L : ℕ → ℕ} {i j x : ℕ} (hij : i < j)
    (hx : x ∈ apBlock (tagResidue j) (tagModulus j) (T j) (L j)) :
    x ≡ 1 [MOD oddPrimeTag i] := by
  exact modEq_of_mem_apBlock
    (oddPrimeTag_dvd_tagModulus_of_le (j := i) (i := j) hij.le)
    (tagResidue_modEq_one_of_lt hij) hx

/-- The tagged AP criterion specialized to the Bertrand prime tags and their
CRT residues. -/
theorem erdos12_positiveSqrtDensity_of_bertrand_tagged_ap_blocks
    {T L E : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c)
    (hE : StrictMono E)
    (hLpos : ∀ i, 0 < L i)
    (hmin : ∀ i, 1 ≤ apMin (tagResidue i) (tagModulus i) (T i))
    (hmax : ∀ i, apMax (tagResidue i) (tagModulus i) (T i) (L i) ≤ E i)
    (hcover : ∀ i, c * Real.sqrt (E (i + 1) : ℝ) ≤ (L i : ℝ))
    (horder :
      ∀ ⦃i j x y : ℕ⦄, i < j →
        x ∈ apBlock (tagResidue i) (tagModulus i) (T i) (L i) →
        y ∈ apBlock (tagResidue j) (tagModulus j) (T j) (L j) →
        x < y)
    (hnarrow :
      ∀ i, 2 * apMax (tagResidue i) (tagModulus i) (T i) (L i) <
        3 * apMin (tagResidue i) (tagModulus i) (T i)) :
    Erdos12PositiveSqrtDensityQuestion := by
  exact erdos12_positiveSqrtDensity_of_tagged_ap_blocks
    (r := tagResidue) (M := tagModulus) (T := T) (L := L) (E := E)
    (q := oddPrimeTag) (c := c)
    hc hE tagModulus_pos hLpos hmin hmax hcover horder hnarrow
    (fun {i} {x} hx => oddPrimeTag_dvd_of_mem_taggedBlock (T := T) (L := L) hx)
    (fun {i} {j} {x} hij hx =>
      taggedBlock_modEq_one_of_lt (T := T) (L := L) hij hx)
    oddPrimeTag_not_dvd_one oddPrimeTag_not_dvd_two

end DivisibilityAvoidingSets
