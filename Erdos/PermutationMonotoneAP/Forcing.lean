import Erdos.PermutationMonotoneAP.Statement

/-!
# Forcing monotone 3-APs: 3-free sets contain no infinite AP

A structural necessary condition for a set `S ⊆ ℕ` to be 3-free (enumerable
avoiding monotone 3-term APs): `S` cannot contain an infinite arithmetic
progression `{c, c + a, c + 2a, …}` (with `a ≥ 1`).

This strengthens Davis–Entringer–Graham–Simmons (the case `S = ℕ`,
`c = 0`, `a = 1`) and is the key obstruction underlying the density bounds for
Erdős problems #195/#196/#197: any 3-free set is "AP-thin".

The proof is a direct (self-contained) version of the DEGS argument applied to
the AP: among the AP elements, let `i_a` index the one appearing earliest in the
enumeration, and `j > i_a` index the earliest-appearing one with larger index;
then the AP element at index `2j - i_a` is forced to appear later still, so
`(c + a·i_a, c + a·j, c + a·(2j - i_a))` is a monotone 3-AP.
-/

namespace PermutationMonotoneAP

open scoped Classical in
/-- If a set `S ⊆ ℕ` contains an infinite arithmetic progression
`{c + a·i : i ∈ ℕ}` with `a ≥ 1`, then *every* enumeration of `S` contains a
monotone 3-term AP. -/
theorem hasMonotoneAP_three_of_containsAP {S : Set ℕ} (e : ℕ ≃ S) {c a : ℕ}
    (ha : 0 < a) (hmem : ∀ i, c + a * i ∈ S) :
    HasMonotoneAP (fun n => (e n : ℕ)) 3 := by
  -- `posOf i` = position of the `i`-th AP element in the enumeration `e`
  set posOf : ℕ → ℕ := fun i => e.symm ⟨c + a * i, hmem i⟩ with hposOf
  -- the value at position `posOf i` is exactly `c + a·i`
  have hval : ∀ i, ((e (posOf i) : S) : ℕ) = c + a * i := by
    intro i; rw [hposOf]; simp
  -- `posOf` is injective
  have hinj : Function.Injective posOf := by
    intro i i' h
    have h1 : (⟨c + a * i, hmem i⟩ : S) = ⟨c + a * i', hmem i'⟩ := e.symm.injective h
    have h2 : c + a * i = c + a * i' := congrArg Subtype.val h1
    have h3 : a * i = a * i' := by omega
    exact Nat.eq_of_mul_eq_mul_left ha h3
  -- `i_a` : an index whose AP element appears earliest
  have hrange : (Set.range posOf).Nonempty := ⟨posOf 0, 0, rfl⟩
  obtain ⟨ia, hia⟩ : sInf (Set.range posOf) ∈ Set.range posOf := Nat.sInf_mem hrange
  have hia_min : ∀ i, posOf ia ≤ posOf i := by
    intro i; rw [hia]; exact Nat.sInf_le ⟨i, rfl⟩
  -- `j` : the index `> ia` whose AP element appears earliest among those
  set T := posOf '' {i | ia < i} with hT
  have hTne : T.Nonempty := ⟨posOf (ia + 1), ia + 1, by simp, rfl⟩
  obtain ⟨j, hj_gt, hj⟩ : sInf T ∈ T := Nat.sInf_mem hTne
  have hjlt : ia < j := hj_gt
  have hj_min : ∀ i, ia < i → posOf j ≤ posOf i := by
    intro i hi; rw [hj]; exact Nat.sInf_le ⟨i, hi, rfl⟩
  -- the three positions are strictly increasing
  have hpos1 : posOf ia < posOf j :=
    lt_of_le_of_ne (hia_min j) fun h => (Nat.ne_of_lt hjlt) (hinj h)
  have ht_gt : ia < 2 * j - ia := by omega
  have hne2 : 2 * j - ia ≠ j := by omega
  have hpos2 : posOf j < posOf (2 * j - ia) :=
    lt_of_le_of_ne (hj_min _ ht_gt) fun h => hne2 (hinj h).symm
  -- assemble the monotone 3-AP at positions posOf ia < posOf j < posOf (2j - ia)
  refine ⟨fun m => match m with
            | 0 => posOf ia | 1 => posOf j | (n + 2) => posOf (2 * j - ia) + n, ?_,
          (c + a * ia : ℕ), (a : ℤ) * ((j : ℤ) - (ia : ℤ)), ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact hpos1
    | 1 => exact hpos2
    | (n + 2) => simp only; omega
  · intro m hm
    have hcast : ((c + a * (2 * j - ia) : ℕ) : ℤ)
        = (c : ℤ) + (a : ℤ) * (2 * (j : ℤ) - (ia : ℤ)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : ia ≤ 2 * j)]; push_cast; ring
    interval_cases m
    · simp only [hval]; push_cast; ring
    · simp only [hval]; push_cast; ring
    · simp only [Nat.add_zero, hval, hcast]; push_cast; ring

/-- A 3-free set contains no infinite arithmetic progression. -/
theorem not_isFree_three_of_containsAP {S : Set ℕ} {c a : ℕ}
    (ha : 0 < a) (hmem : ∀ i, c + a * i ∈ S) : ¬ IsFree S 3 := by
  rintro ⟨e, he⟩
  exact he (hasMonotoneAP_three_of_containsAP e ha hmem)

/-- **A 3-free set misses infinitely many terms of every infinite AP.** For a
3-free `S`, any arithmetic progression `c, c+a, c+2a, …` (with `a ≥ 1`) has
infinitely many terms outside `S`. (Otherwise `S` would contain a tail of the
AP — itself an infinite AP — contradicting `not_isFree_three_of_containsAP`.) -/
theorem isFree_three_missesAP_infinite {S : Set ℕ} (h : IsFree S 3)
    {a : ℕ} (ha : 0 < a) (c : ℕ) : {i : ℕ | c + a * i ∉ S}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have htail : ∀ j, (c + a * (N + 1)) + a * j ∈ S := by
    intro j
    by_contra hnj
    have hmem : (N + 1) + j ∈ {i : ℕ | c + a * i ∉ S} := by
      simp only [Set.mem_setOf_eq]
      rw [show c + a * ((N + 1) + j) = (c + a * (N + 1)) + a * j by ring]
      exact hnj
    have := hN hmem
    omega
  exact not_isFree_three_of_containsAP ha htail h

/-- **A 3-free set is co-infinite**: if `S` is 3-free then `ℕ \ S` is infinite.
The weakest rung toward the open density upper bound (`β(3) < 1`, …): a 3-free
set cannot be cofinite. -/
theorem isFree_three_compl_infinite {S : Set ℕ} (h : IsFree S 3) : Sᶜ.Infinite := by
  have key := isFree_three_missesAP_infinite h (a := 1) one_pos 0
  simpa using key

/-- `ℕ` itself is not 3-free — the Davis–Entringer–Graham–Simmons theorem, phrased
via the framework (every enumeration of `ℕ` contains a monotone 3-AP). -/
theorem not_isFree_univ : ¬ IsFree (Set.univ : Set ℕ) 3 := by
  intro h
  have hcompl := isFree_three_compl_infinite h
  rw [Set.compl_univ] at hcompl
  exact hcompl Set.finite_empty

/-- **3-freeness is downward closed.** Any infinite subset of a 3-free set is
itself 3-free: restrict the enumeration to the subset (in the order it appears).
A monotone 3-AP in the restricted enumeration is one in the original. -/
theorem isFree_three_of_subset {S S' : Set ℕ} (hS : IsFree S 3) (hsub : S' ⊆ S)
    (hinf : S'.Infinite) : IsFree S' 3 := by
  obtain ⟨e, he⟩ := hS
  -- positions in the `S`-enumeration whose value lands in `S'`
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
  -- the restricted enumeration `g : ℕ → S'`
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
        rw [Equiv.apply_symm_apply]; exact hs
      obtain ⟨n, hn⟩ := Nat.subset_range_nth (p := p) hm
      refine ⟨n, Subtype.ext ?_⟩
      change (e (Nat.nth p n) : ℕ) = s
      rw [hn, Equiv.apply_symm_apply]
  refine ⟨Equiv.ofBijective g hgbij, ?_⟩
  intro hmono
  apply he
  obtain ⟨pos, hposmono, a, d, hAP⟩ := hmono
  refine ⟨fun j => Nat.nth p (pos j), (Nat.nth_strictMono hpinf).comp hposmono, a, d, ?_⟩
  intro j hj
  exact hAP j hj

/-- **Affine invariance of 3-freeness.** The affine image `{c + a·t : t ∈ T}`
(with `a ≥ 1`) of a 3-free set `T` is 3-free. The map `t ↦ c + a·t` is an
order- and AP-isomorphism, so it carries the avoiding enumeration over. -/
theorem isFree_three_affine_image {T : Set ℕ} (hT : IsFree T 3) {a c : ℕ} (ha : 0 < a) :
    IsFree ((fun t => c + a * t) '' T) 3 := by
  obtain ⟨e, he⟩ := hT
  have hinj : Function.Injective (fun t : ℕ => c + a * t) := by
    intro x y h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left ha (by omega)
  refine ⟨e.trans (Equiv.Set.image _ T hinj), ?_⟩
  intro hmono
  apply he
  obtain ⟨pos, hposmono, A, D, hAP⟩ := hmono
  have hval : ∀ n, (((e.trans (Equiv.Set.image (fun t => c + a * t) T hinj)) n : ℕ))
      = c + a * (e n : ℕ) := fun n => rfl
  simp only [hval] at hAP
  have h0 := hAP 0 (by omega)
  have h1 := hAP 1 (by omega)
  have h2 := hAP 2 (by omega)
  push_cast at h0 h1 h2
  have haz : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have he2 : ((e (pos 2) : ℕ) : ℤ)
      = 2 * ((e (pos 1) : ℕ) : ℤ) - ((e (pos 0) : ℕ) : ℤ) := by
    have hk : (a : ℤ) * ((e (pos 2) : ℕ) : ℤ)
        = (a : ℤ) * (2 * ((e (pos 1) : ℕ) : ℤ) - ((e (pos 0) : ℕ) : ℤ)) := by
      nlinarith [h0, h1, h2]
    exact mul_left_cancel₀ haz hk
  refine ⟨pos, hposmono, ((e (pos 0) : ℕ) : ℤ),
    ((e (pos 1) : ℕ) : ℤ) - ((e (pos 0) : ℕ) : ℤ), ?_⟩
  intro j hj
  interval_cases j
  · push_cast; ring
  · push_cast; ring
  · push_cast; rw [he2]; ring

/-- **Converse affine invariance.** If the affine image `{c + a·t : t ∈ T}`
(with `a ≥ 1`) is 3-free, then `T` is 3-free. (Pull the enumeration back along
the affine bijection.) -/
theorem isFree_three_of_affine_image {T : Set ℕ} {a c : ℕ} (ha : 0 < a)
    (h : IsFree ((fun t => c + a * t) '' T) 3) : IsFree T 3 := by
  obtain ⟨e', he'⟩ := h
  have hinj : Function.Injective (fun t : ℕ => c + a * t) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left ha (by omega)
  set φ' := Equiv.Set.image (fun t => c + a * t) T hinj with hφ'
  refine ⟨e'.trans φ'.symm, ?_⟩
  intro hmono
  apply he'
  obtain ⟨pos, hposmono, a', d', hAP⟩ := hmono
  have hinv : ∀ n, (c : ℤ) + (a : ℤ) * (((e'.trans φ'.symm) n : ℕ) : ℤ) = ((e' n : ℕ) : ℤ) := by
    intro n
    have h1 : φ' (φ'.symm (e' n)) = e' n := φ'.apply_symm_apply (e' n)
    have h2 : ((φ' (φ'.symm (e' n)) : ℕ)) = ((e' n : ℕ)) := congrArg Subtype.val h1
    have h3 : ((φ' (φ'.symm (e' n)) : ℕ)) = c + a * ((φ'.symm (e' n) : ℕ)) := rfl
    rw [h3] at h2
    have h4 : ((e'.trans φ'.symm) n : ℕ) = (φ'.symm (e' n) : ℕ) := rfl
    rw [h4]; exact_mod_cast h2
  refine ⟨pos, hposmono, (c : ℤ) + (a : ℤ) * a', (a : ℤ) * d', ?_⟩
  intro j hj
  have hAPj := hAP j hj
  rw [← hinv (pos j), hAPj]; ring

/-- **Self-similarity of 3-freeness.** If `S` is 3-free, then for any AP
`c, c+a, c+2a, …` (with `a ≥ 1`) the AP-restriction `{i : c + a·i ∈ S}` is 3-free
(when infinite). Hence a 3-free set has density `≤ α(3)` in every residue class. -/
theorem isFree_three_apRestrict {S : Set ℕ} (hS : IsFree S 3) {a c : ℕ} (ha : 0 < a)
    (hinf : {i | c + a * i ∈ S}.Infinite) : IsFree {i | c + a * i ∈ S} 3 := by
  have hinj : Function.Injective (fun t : ℕ => c + a * t) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left ha (by omega)
  have himg_sub : (fun t => c + a * t) '' {i | c + a * i ∈ S} ⊆ S := by
    rintro _ ⟨i, hi, rfl⟩; exact hi
  have himg_inf : ((fun t => c + a * t) '' {i | c + a * i ∈ S}).Infinite :=
    hinf.image (hinj.injOn)
  exact isFree_three_of_affine_image ha (isFree_three_of_subset hS himg_sub himg_inf)

/-- **A 3-AP-free set is 3-free.** If an infinite set `S` contains no 3-term AP
at all, then any enumeration avoids monotone 3-APs (vacuously) — so `S` is 3-free.
In particular `IsFree _ 3` is inhabited (e.g. by sparse sets like powers of two). -/
theorem isFree_three_of_no_threeAP {S : Set ℕ} (hinf : S.Infinite)
    (hno : ∀ x d : ℕ, 0 < d → x ∈ S → x + d ∈ S → x + 2 * d ∈ S → False) : IsFree S 3 := by
  classical
  haveI : Infinite (S : Set ℕ) := hinf.to_subtype
  haveI : Denumerable (S : Set ℕ) := Denumerable.ofEncodableOfInfinite _
  refine ⟨(Denumerable.eqv (S : Set ℕ)).symm, ?_⟩
  rintro ⟨pos, hpos, a, d, hAP⟩
  set e := (Denumerable.eqv (S : Set ℕ)).symm with he
  set v0 := (e (pos 0) : ℕ) with hv0d
  set v1 := (e (pos 1) : ℕ) with hv1d
  set v2 := (e (pos 2) : ℕ) with hv2d
  have hv0 : v0 ∈ S := (e (pos 0)).2
  have hv1 : v1 ∈ S := (e (pos 1)).2
  have hv2 : v2 ∈ S := (e (pos 2)).2
  have e0 := hAP 0 (by omega)
  have e1 := hAP 1 (by omega)
  have e2 := hAP 2 (by omega)
  have hsum : v0 + v2 = 2 * v1 := by push_cast at e0 e1 e2; omega
  have hne : v0 ≠ v2 := by
    intro h
    have h' : e (pos 0) = e (pos 2) := Subtype.ext h
    have := e.injective h'
    have h02 : pos 0 < pos 2 := hpos (by omega)
    omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact hno v0 (v1 - v0) (by omega) hv0 (by rw [Nat.add_sub_cancel' (by omega)]; exact hv1)
      (by rw [show v0 + 2 * (v1 - v0) = v2 by omega]; exact hv2)
  · exact hno v2 (v1 - v2) (by omega) hv2 (by rw [Nat.add_sub_cancel' (by omega)]; exact hv1)
      (by rw [show v2 + 2 * (v1 - v2) = v0 by omega]; exact hv0)

end PermutationMonotoneAP
