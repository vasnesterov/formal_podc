import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Safety

/-!
# A false sentence in the proof of Lemma 7

The proof of Lemma 7 claims: "every low level write in `r` that is triggered after time `t` [when
`W` returns] is associated with a bigger timestamp than `ts`". This is false: an idle writer whose
stale low-level write (from its write before last) responds re-triggers a write with its own,
older, `tsVal` (lines 29–32).

Run (correct layout `n = 3`, `f = 1`, `k = 2`, `z = 1`: writer `0` uses registers `0, 1, 2`, writer
`1` uses `3, 4, 5`, register `b` on server `b mod 3`): writer 0 writes `1` (its write on register 2
stays pending), then writes `2` (register 2 is in its `coverSet`), writer 1 writes `3`
(timestamp 3) and returns; then writer 0's first write on register 2 responds and writer 0
re-triggers `write(2, 2)` on register 2 — after the write with timestamp 3 returned. The conclusion
of Lemma 7 survives: such re-triggers only hit registers the writer already covered (`count` in
`Algorithm2Safety.lean`).
-/

namespace Podc.RegisterEmulationSpace.Alg2.Lemma7

/-- Servers of the registers. -/
def δ (b : Fin 6) : Fin 3 := ⟨b.val % 3, Nat.mod_lt _ (by omega)⟩

/-- Write sets. -/
def R (c : Fin 2) : Finset (Fin 6) := if c = 0 then {0, 1, 2} else {3, 4, 5}

/-- Up to the return of the write of `3` by writer 1. -/
def E₁ : List (Ev (Fin 2) ℕ) :=
  [.inv 0 (.write 1)] ++ List.replicate 6 (.step 0) ++ (List.range 6).map (.resp 0) ++
    List.replicate 4 (.step 0) ++ [.resp 0 6, .resp 0 7, .step 0] ++
  [.inv 0 (.write 2)] ++ List.replicate 6 (.step 0) ++ ((List.range 6).map (· + 9)).map (.resp 0) ++
    List.replicate 3 (.step 0) ++ [.resp 0 15, .resp 0 16, .step 0] ++
  [.inv 1 (.write 3)] ++ List.replicate 6 (.step 1) ++ (List.range 6).map (.resp 1) ++
    List.replicate 4 (.step 1) ++ [.resp 1 6, .resp 1 7, .step 1]

/-- The stale write responds and writer 0 re-triggers. -/
def E₂ : List (Ev (Fin 2) ℕ) := [.resp 0 8, .step 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- After the write with timestamp 3 has returned (sequential history of three writes), the low-level
write number 17 of writer 0, triggered afterwards, carries timestamp 2. -/
theorem retrigger_old_timestamp :
    ((alg δ 1 R 0).run E₁).hist =
        seqHist [((0 : Fin 2), HOp.write 1, 1), (0, .write 2, 2), (1, .write 3, 3)] ∧
      (((alg δ 1 R 0).run E₁).loc 1).ts = 3 ∧
      ((alg δ 1 R 0).run E₁).cnt 0 = 17 ∧
      ((alg δ 1 R 0).run (E₁ ++ E₂)).pend 0 = [⟨17, 2, .write (2, 2)⟩] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Podc.RegisterEmulationSpace.Alg2.Lemma7
