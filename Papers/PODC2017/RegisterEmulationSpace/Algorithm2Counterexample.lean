import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Reg

/-!
# The paper's client-to-set mapping `j = ⌊i/z⌋` breaks Algorithm 2

Appendix D assigns client `c_i` (`1 ≤ i ≤ k`) to the register set `R_⌊i/z⌋`. With 1-based `i` the
set `R_0` gets `z - 1` writers and the last set gets one writer more than it is sized for (and if
`z ∣ k`, client `c_k` is mapped to the non-existent set `R_m`).

Smallest instance: `n = 4`, `f = 1`, `k = 3`, so `z = 2`, `m = 2`, `|R_0| = 4`,
`|R_1| = (k - ⌊k/z⌋ z) f + f + 1 = 3`; clients `c_2, c_3` both use `R_1 = {a, b, c}` (registers 4, 5, 6
on servers 0, 1, 2), which only accommodates one writer. Sequential run:
1. `c_2` writes `1`: `(1,1)` lands on `a, b`; its write on `c` stays pending; `c_2` returns.
2. `c_3` writes `2` (it reads timestamp 1): `(2,2)` lands on `c` and `a`, its write on `b` stays
   pending; `c_3` returns.
3. `c_2`'s old write `(1,1)` lands on `c`. Now `a = (2,2)`, `b = c = (1,1)`.
4. `c_1` reads, hearing from servers 1, 2, 3 (all registers except those on server 0, which holds `a`):
   maximum `(1,1)`, it returns `1` although the last write wrote `2`.

`not_seqSafe_paperMapping` checks this run of our formalization of Algorithm 2 (`alg`) by evaluation.
-/

namespace Podc.RegisterEmulationSpace.Alg2.Counterexample

open Finset

/-- Servers `0..3`; registers `0..3` form `R_0`, registers `4, 5, 6` form `R_1`. -/
def δ (b : Fin 7) : Fin 4 := if h : b.val < 4 then ⟨b.val, h⟩ else ⟨b.val - 4, by omega⟩

/-- The paper's mapping: client `c_i` is `Fin 3` index `i - 1`; `c_1 ↦ R_0`, `c_2, c_3 ↦ R_1`. -/
def R (c : Fin 3) : Finset (Fin 7) := if c = 0 then {0, 1, 2, 3} else {4, 5, 6}

/-- The paper's set index `⌊i/z⌋` for `n = 4, f = 1, k = 3` (`z = 2`). -/
lemma paper_index : (fun i : ℕ => i / ((4 - (1 + 1)) / 1)) 1 = 0 ∧
    (fun i : ℕ => i / ((4 - (1 + 1)) / 1)) 2 = 1 ∧ (fun i : ℕ => i / ((4 - (1 + 1)) / 1)) 3 = 1 := by
  decide

/-- The sizes prescribed by the paper: `|R_0| = zf + f + 1 = 4`, `|R_1| = (k - ⌊k/z⌋z)f + f + 1 = 3`. -/
lemma paper_sizes : #(R 0) = 2 * 1 + 1 + 1 ∧ #(R 1) = (3 - 3 / 2 * 2) * 1 + 1 + 1 ∧ R 1 = R 2 := by
  decide

/-- The capacity condition fails for `R_1` (two writers, room for one). -/
lemma not_layout : ¬ Layout δ 1 univ R := by
  intro h
  have := h.cap 1 (mem_univ _)
  revert this
  decide

/-- The run. -/
def E : List (Ev (Fin 3) ℕ) :=
  [.inv 1 (.write 1)] ++ List.replicate 7 (.step 1) ++ (List.range 7).map (.resp 1) ++
    List.replicate 4 (.step 1) ++ [.resp 1 7, .resp 1 8, .step 1] ++
  [.inv 2 (.write 2)] ++ List.replicate 7 (.step 2) ++ (List.range 7).map (.resp 2) ++
    List.replicate 4 (.step 2) ++ [.resp 2 9, .resp 2 7, .step 2] ++
  [.resp 1 9] ++
  [.inv 0 .read] ++ List.replicate 7 (.step 0) ++ [.resp 0 1, .resp 0 2, .resp 0 3, .resp 0 5,
    .resp 0 6, .step 0]

set_option maxRecDepth 100000 in
lemma hist_E : ((alg δ 1 R 0).run E).hist =
    seqHist [((1 : Fin 3), HOp.write 1, 1), (2, .write 2, 2), (0, .read, 1)] := by
  rfl

/-- **Counterexample** (paper's mapping `j = ⌊i/z⌋`): Algorithm 2 is not even safe in sequential
runs: after the writes of `1` and `2`, a read returns `1`. -/
theorem not_seqSafe_paperMapping : ¬ (alg δ 1 R 0).SeqSafe 0 Set.univ := by
  intro h
  have := h E [((1 : Fin 3), HOp.write 1, 1), (2, .write 2, 2)] 0 1 hist_E (by simp)
  simp [lastVal] at this

set_option maxRecDepth 100000 in
/-- The same run violates WS-Regularity (so `WSRegular` is not vacuous). -/
theorem not_wsRegular_paperMapping : ¬ WSRegular (alg δ 1 R 0) 0 Set.univ := by
  intro h
  have hws : (hscan 0 ((alg δ 1 R 0).run E).hist).ws := by
    rw [hist_E]; simp [hscan, hinit, hstep, seqHist, isW]
  have := h E (fun _ _ _ => Set.mem_univ _) hws
  rw [hist_E] at this
  simp [hscan, hinit, hstep, seqHist, valOf, Function.update] at this
  obtain ⟨t, h1, h2, h3⟩ := this
  obtain rfl : t = 2 := by omega
  simp at h3

end Podc.RegisterEmulationSpace.Alg2.Counterexample
