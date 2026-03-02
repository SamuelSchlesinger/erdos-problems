/-
# Upper Bounds on Sum-Free Sets

Since SumFree implies TripleFree (Problem 301 generalizes Problem 302),
every upper bound on triple-free sets immediately gives an upper bound
on sum-free sets. In particular, van Doorn's 9/10 bound transfers:

  f₃₀₁(N) ≤ f₃₀₂(N) ≤ (9/10 + o(1))N.

This is the first formalized upper bound for Problem 301.
-/
import Erdos.UnitFractionSets.Connections
import Erdos.UnitFractionTriples.VanDoorn

namespace UnitFractionSets

open UnitFractionTriples UnitFractionConnections

/-- **Van Doorn's 9/10 bound transfers to sum-free sets.**

    Since SumFree A implies TripleFree A, the structural bound
    A.card + |D_S| + |D_T| ≤ N from van Doorn's triple-free analysis
    applies directly to any sum-free set A ⊆ {1, …, N}.

    Combined with the density estimates |D_S| ≈ N/18 and |D_T| ≈ N/120,
    this gives f₃₀₁(N) ≤ 9N/10 + o(N). -/
theorem sum_free_van_doorn_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter SParam).card
           + ((Finset.Icc 1 (N / 20)).filter TParam).card ≤ N :=
  van_doorn_upper_bound N A (sumFree_implies_tripleFree hA) hAN

end UnitFractionSets
