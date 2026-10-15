import Papers.PODC2016.TwoBitRegisters.InvHist

/-!
# Safety: the register is atomic (Lemmas 2–5 and 10, Theorem 1 safety part)

Mostéfaoui, Raynal, *Two-Bit Messages are Sufficient to Implement Atomic Read/Write Registers in
Crash-prone Systems*, PODC 2016 (arXiv:1602.02695).

All statements quantify over every reachable configuration `C` with history `h` of
`alg w t v₀` (asynchronous, unordered reliable channels, any number of crashes, any number of
operations); the only assumption is `2 t < n` (the quorum size is `n - t`).
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V} {h : List (Label P (register V v₀))}

/-- **Lemma 2** of the paper: `w_sync_i[i] ≥ w_sync_j[i]`. -/
theorem lemma2 (hr : (alg w t v₀).Reach C h) (i j : P) : W C j i ≤ W C i i := by
  by_cases hij : i = j
  · subst hij; exact le_refl _
  · exact ((invW_of_reach hr).recv_le i j hij).trans (InvW.sent_le_own C i j)

/-- **Lemma 3** of the paper: `w_sync_i[i] = max_j w_sync_i[j]`. -/
theorem lemma3 (hr : (alg w t v₀).Reach C h) (i j : P) : W C i j ≤ W C i i :=
  (invW_of_reach hr).ws_le i j

/-- **Lemma 4** of the paper: `history_i[0..w_sync_i[i]]` is a prefix of the writer's history,
which consists of the initial value followed by the written values. -/
theorem lemma4 (ht : 2 * t < Fintype.card P) (hr : (alg w t v₀).Reach C h) (i : P) (k : ℕ)
    (hk : k ≤ W C i i) : (C.loc i).hist k = writeVal v₀ (opsOf h w) k := by
  obtain ⟨g, hH⟩ := invH_of_reach ht hr
  have hI := invW_of_reach hr
  rw [hI.hist i k hk]
  exact hH.hist_w k (hk.trans (hI.own_le i))

/-- **Lemma 5** of the paper, channel part. Here `sent C i j = min(w_sync_i[i], w_sync_i[j] + 1)` is
a formula on local variables; that it equals the number of `WRITE` messages `p_i` has actually sent
to `p_j` (the paper's R1/R2) is `lemma5_sent` in `Messages.lean`. The messages not yet processed by
`p_j` are exactly the numbers `k ∈ (w_sync_j[i], sent C i j]`, the `k`-th one being
`WRITE(k mod 2, v_k)`; there are at most two of them (Property P1) — unless `p_i` crashed, in
which case some may be lost. -/
theorem lemma5 (hr : (alg w t v₀).Reach C h) (i j : P) (hij : i ≠ j) :
    W C j i ≤ sent C i j ∧ sent C i j ≤ W C j i + 2 ∧
    (∀ b v, (i, j, Msg.write b v) ∈ C.net →
      ∃ k, W C j i < k ∧ k ≤ sent C i j ∧ b = par k ∧ v = Hw w C k) ∧
    (i ∉ C.crashed → ∀ k, W C j i < k → k ≤ sent C i j →
      (i, j, Msg.write (par k) (Hw w C k)) ∈ C.net) := by
  have hI := invW_of_reach hr
  refine ⟨hI.recv_le i j hij, hI.sent_le_two hij, fun b v hm => ?_, fun hi k h1 h2 => ?_⟩
  · exact (hI.net_write i j b v (Multiset.count_pos.2 hm)).2
  · exact Multiset.count_pos.1 (hI.exact i j k hij hi h1 h2)

/-- **Lemma 10** of the paper (the three claims). Let `rf x` be the index of the value returned by
a completed read `x` (`0` = initial value, `m` = value of the `m`-th write `(w, m - 1)`):
* Claim 1 (no read from the future): a read does not complete before the write it reads from is
  invoked;
* Claim 2 (no overwritten value): if write `(w, rf x)` (the next write) completes before the read
  `x` starts, contradiction;
* Claim 3 (no new/old inversion): if read `x` completes before read `y` starts, `rf x ≤ rf y`. -/
theorem lemma10 (ht : 2 * t < Fintype.card P) (hr : (alg w t v₀).Reach C h) :
    ∃ rf : OpId P → ℕ,
      (∀ x : OpId P, x.1 ≠ w → Completed h x →
        respOf h x = some (writeVal v₀ (opsOf h w) (rf x))) ∧
      (∀ x : OpId P, x.1 ≠ w → Completed h x → 0 < rf x → ¬ Precedes h x (w, rf x - 1)) ∧
      (∀ x : OpId P, x.1 ≠ w → Completed h x → ¬ Precedes h (w, rf x) x) ∧
      (∀ x y : OpId P, x.1 ≠ w → y.1 ≠ w → Completed h y → Precedes h x y → rf x ≤ rf y) := by
  obtain ⟨g, hH⟩ := invH_of_reach ht hr
  exact ⟨g.rf, hH.read_val, hH.not_future, hH.not_overwritten, hH.mono⟩

/-- **Theorem 1 (safety part)**: every execution of the algorithm of Figure 1 has a linearizable
history, i.e. the algorithm implements an atomic SWMR register (process `w` writes, all other
processes read) in `CAMP_{n,t}[t < n/2]`. Channels are unordered; any number of processes may
crash (safety does not need the bound on crashes, only the quorum size `n - t > n/2`). -/
theorem linearizable (ht : 2 * t < Fintype.card P) : (alg w t v₀).Linearizable := by
  intro C h hr
  obtain ⟨g, hH⟩ := invH_of_reach ht hr
  exact ⟨swmrLin h w g.rf, SWMRReadsFrom.isLinearization
    ⟨hH.wf, hH.ops, hH.write_resp, hH.read_val, hH.not_future, hH.not_overwritten, hH.mono⟩⟩

end Podc.TwoBit
