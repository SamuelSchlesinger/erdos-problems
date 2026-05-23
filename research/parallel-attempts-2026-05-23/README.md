# Parallel scout attempts (2026-05-23)

Thirteen parallel agents were dispatched, each in an isolated git worktree, to
attack one tractable handhold from the cross-project handhold synthesis. The
agents were stopped before they could all finish.

## Outcomes

- **Merged**: UlamPrimeRecurrence (length-10 chain), PracticalNumbers (4 +
  sparsity of 3 and 5).
- **Patches saved here** (unverified — written but not built or committed):
  - `agent-a8d4afa3.patch` — ConsecutivePowerful mod-100 obstruction (+26 lines)
  - `agent-a9fb3de9.patch` — WeirdNumbers verify 4030, 5830 (+124 lines)
  - `agent-a89f34ab.patch` — DistinctDistances linear lower bound (+119 lines)
  - `agent-adc1ab2d.patch` — MaximalSidonSets T0 sharper cubic (+244 lines)
  - `AlmostSidon-SidonInterval.lean` — KST/Lindström Sidon-interval bound,
    new file (327 lines)
- **No progress**: ErdosMoser mod-1820, PrimaryPseudoperfect 47058,
  UnitFractionTriples StarNeighborhood, UnitFractionSets 145/168,
  ConsecutivePowerful abc-conditional, WeirdNumbers odd_weird_four_prime_factors.

## Resurrection

Each patch was generated against `f74f2a0` (project HEAD at session start).
Apply with `git apply research/parallel-attempts-2026-05-23/<file>.patch` and
run `lake build` to validate. Agents had not finished build verification when
stopped; expect minor errors.
