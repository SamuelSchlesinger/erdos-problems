import Erdos.RegularInducedSubgraphs.Statement

/-
# Elementary Facts About Regular Induced Subgraphs

This file records the first universal lower bound for Erdős problem `#82`.
The empty induced subgraph and every one-vertex induced subgraph are regular,
so every graph with at least one vertex forces a regular induced subgraph of
order `1`.
-/
namespace RegularInducedSubgraphs

open SimpleGraph

variable {α : Type*}

/-- The empty induced subgraph is regular, vacuously. -/
@[simp] theorem isRegularOn_empty (G : SimpleGraph α) :
    IsRegularOn G ∅ := by
  simp [IsRegularOn]

/-- A one-vertex induced subgraph is regular: there is only one selected vertex,
so all selected induced degrees agree. -/
@[simp] theorem isRegularOn_singleton (G : SimpleGraph α) (v : α) :
    IsRegularOn G ({v} : Finset α) := by
  intro u hu w hw
  simp at hu hw
  subst u
  subst w
  rfl

/-- Every graph on a nonempty vertex type contains a regular induced subgraph
with exactly one vertex. -/
theorem exists_regularInducedSubgraph_card_one [Nonempty α] (G : SimpleGraph α) :
    ∃ s : Finset α, s.card = 1 ∧ IsRegularOn G s := by
  let v : α := Classical.arbitrary α
  exact ⟨{v}, by simp, isRegularOn_singleton G v⟩

/-- Equivalently, every graph on a nonempty vertex type contains a regular
induced subgraph on at least one vertex. -/
theorem hasRegularInducedSubgraph_one [Nonempty α] (G : SimpleGraph α) :
    HasRegularInducedSubgraph G 1 := by
  obtain ⟨s, hcard, hs⟩ := exists_regularInducedSubgraph_card_one G
  exact ⟨s, by omega, hs⟩

/-- Therefore the forcing threshold in problem `#82` is at least `1` whenever
the ambient graph has a nonempty vertex set. -/
theorem forcesRegularInducedSubgraph_one {n : ℕ} (hn : 0 < n) :
    ForcesRegularInducedSubgraph n 1 := by
  intro G
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hasRegularInducedSubgraph_one G

/-- In terms of `FValue`, the elementary forcing bound says `1 ≤ F(n)` for
all positive `n`. -/
theorem one_le_FValue {n : ℕ} (hn : 0 < n) :
    1 ≤ FValue n := by
  classical
  unfold FValue
  exact Nat.le_findGreatest (P := ForcesRegularInducedSubgraph n) (m := 1) (n := n) hn
    (forcesRegularInducedSubgraph_one hn)

end RegularInducedSubgraphs
