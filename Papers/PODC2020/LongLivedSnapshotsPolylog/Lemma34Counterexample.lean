import Papers.PODC2020.LongLivedSnapshotsPolylog.Counterexample

/-!
# Lemma 3.4 is false as stated

Lemma 3.4: in a `b`-bounded-increment execution, if `K ≥ 2` unsuccessful loop iterations are
performed by a `CompScan` instance `S`, then at least `⌈(K - 2) m / b⌉` instances of `MaxUpdate`
*start* during the execution interval of `S`.

The proof counts the `WriteMax` operations that take effect during `S` and then claims that each
belongs to a `MaxUpdate` that started during `S`. But up to `n - 1` `MaxUpdate`s may have
started before `S` and write during `S`. Counterexample with `n = 4`, `m = 16 = n²`, `b = 4`
(the paper's parameters), `K = 3` (and helping period `X = 4`): processes `A = 0`, `B = 1`,
`C = 2` have invoked `MaxUpdate(left, 16)`, `MaxUpdate(right, 16)`, `MaxUpdate(left, 20)` before
`S = 3` invokes `MaxScan` (with `MR_left = MR_right = 15`); then

1. `A` writes `16` to `MR_left` during the first iteration of `S` (line 18 fails);
2. `B` writes `16` to `MR_right` during the second iteration (line 18 fails);
3. `C` writes `20`, completes, and runs `MaxUpdate(left, 24)`, `(left, 28)`, `(left, 32)` during
   the third iteration (line 18 fails).

`S` has performed `3` unsuccessful iterations (its counter `c` is `3`), only `3` `MaxUpdate`s
were invoked during `S`, but `⌈(3 - 2)·16/4⌉ = 4` (`lemma_3_4_false`).

Lemma 3.5 (wait-freedom) survives: its proof only needs the number of `WriteMax` steps during the
iterations, see `WaitFree.lemma_3_4` and `WaitFree.iterations_le`.
-/

namespace Podc.LongLivedSnapshotsPolylog.Counterexample34

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)
open Podc.LongLivedSnapshotsPolylog.Counterexample (writesTo_eq)

/-- Labels of the counterexample. -/
abbrev L4 := Label (Fin 4) maxArrObj

/-- A complete solo `MaxUpdate` (operation `o`) of process `p`. -/
def solo (p : Fin 4) (o : MAOp) : List L4 :=
  [.inv p o] ++ List.replicate 10 (.tau p) ++ [.ret p (0, 0)]

/-- The prefix before `S` invokes `MaxScan`: `MR_left = MR_right = 15`, and the pending
invocations of `A`, `B`, `C`. -/
def αpre : List L4 :=
  solo 0 (.upd0 4) ++ solo 0 (.upd0 8) ++ solo 0 (.upd0 12) ++ solo 0 (.upd0 15) ++
  solo 1 (.upd1 4) ++ solo 1 (.upd1 8) ++ solo 1 (.upd1 12) ++ solo 1 (.upd1 15) ++
  [.inv 0 (.upd0 16), .inv 1 (.upd1 16), .inv 2 (.upd0 20)]

/-- The part after the invocation of `S`'s `MaxScan`. -/
def βpost : List L4 :=
  -- iteration 1: `A` writes `16` before the first read of line 18
  List.replicate 6 (.tau 3) ++ [.tau 0] ++ [.tau 3] ++
  -- iteration 2: `B` writes `16` before the second read of line 18
  List.replicate 6 (.tau 3) ++ [.tau 1] ++ [.tau 3, .tau 3] ++
  -- iteration 3: `C` writes `20`, completes, and runs three more `MaxUpdate`s
  List.replicate 6 (.tau 3) ++ List.replicate 10 (.tau 2) ++ [.ret 2 (0, 0)] ++
  solo 2 (.upd0 24) ++ solo 2 (.upd0 28) ++ solo 2 (.upd0 32) ++ [.tau 3]

/-- Invocations of `MaxUpdate`. -/
def isUpdInv : L4 → Bool
  | .inv _ (.upd0 _) => true
  | .inv _ (.upd1 _) => true
  | _ => false

/-- **Lemma 3.4 of the paper is false.** In a `4`-bounded-increment execution of Algorithm 1
with `n = 4`, `m = 16`, the `CompScan` of the pending `MaxScan` of process `3` has performed
`K = 3` unsuccessful iterations (its iteration counter is `3`, it is about to start the fourth
iteration), only `3` `MaxUpdate`s were invoked after the invocation of the `MaxScan`, whereas
Lemma 3.4 claims at least `⌈(K - 2) m / b⌉ = 4`. -/
theorem lemma_3_4_false :
    ∃ α β : List L4, (alg1 4 16 4).Valid (α ++ .inv 3 .scan :: β) ∧
      BIExec 4 16 4 4 (α ++ .inv 3 .scan :: β) ∧ (∀ r, .ret 3 r ∉ β) ∧
      (∃ C, (alg1 4 16 4).run (α ++ .inv 3 .scan :: β) = some C ∧
        (C.loc 3).pc = .rdR1 ⟨false, 3, none⟩) ∧
      (β.filter isUpdInv).length = 3 ∧ 3 < ((3 - 2) * 16 + 4 - 1) / 4 := by
  refine ⟨αpre, βpost, Impl.valid_of_crun _ (by decide +kernel), ?_, ?_, ?_,
    by decide +kernel, by decide⟩
  · intro sd
    rw [writesTo_eq (alg1 4 16 4), boundedIncr_iff_stepBounded]
    unfold StepBounded
    revert sd
    decide +kernel
  · intro r hr
    simp [βpost, solo] at hr
  · rw [(alg1 4 16 4).run_eq_crun]
    have h : ((alg1 4 16 4).crun (αpre ++ Label.inv 3 MAOp.scan :: βpost)).map
        (fun C => (C.loc 3).pc) = some (.rdR1 ⟨false, 3, none⟩) := by decide +kernel
    cases hC : (alg1 4 16 4).crun (αpre ++ .inv 3 .scan :: βpost) with
    | none => rw [hC] at h; cases h
    | some C =>
      rw [hC] at h
      exact ⟨C, rfl, Option.some.inj h⟩

end Podc.LongLivedSnapshotsPolylog.Counterexample34
