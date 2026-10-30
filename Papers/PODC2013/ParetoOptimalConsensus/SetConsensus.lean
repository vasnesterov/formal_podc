import Papers.PODC2016.UnbeatableSetConsensus.Counterexample
import Papers.PODC2016.UnbeatableSetConsensus.Unbeatable

/-!
# The `k`-set consensus part (§4, Appendix B): bridge to the 2016 formalization

The protocol `Opt_min-k` of §4 is the protocol `Optmin[k]` of the journal-style PODC 2016 paper by
the same authors, formalized in `Papers.PODC2016.UnbeatableSetConsensus` (same model, same
definitions of hidden nodes, hidden capacity (Definition 2), `Vals`, `Min`, low/high
(Definition 1)). We restate its results with the numbering of this paper:

* **Lemma 4** (`lemma4`): `Opt_min-k` solves `k`-set consensus, decisions by `⌊f/k⌋ + 1`.
* **Lemma 9** = Lemma 2 of the 2016 paper (`ChainHyp`, `chainRun` and its properties).
* **Lemma 10 is false as stated** (`lemma10_false`): it is Lemma 1 of the 2016 paper, with the
  same five conditions (alive; low for the first time; a single low value `v`; hidden capacity
  `≥ k - 1`; `k` processes high at `m - 1` hidden at `m`). Counterexample with `n = 6`, `k = 2`,
  `t = 1`, `V = {0, 1, 2}`.
* **Lemma 11** = Lemma 3 of the 2016 paper (`lemma11`, proved via the corrected Lemma 10).
* **Theorem 4** (`theorem4`): `Opt_min-k` is unbeatable.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {k t : ℕ} {D : Set ℕ}

/-- **Lemma 4.** `Opt_min-k` solves `k`-set consensus; every process alive at `⌊f/k⌋ + 1` has
decided by then. -/
theorem lemma4 (hk : 0 < k) :
    SolvesSetConsensus k t D (optmin k : Protocol P) ∧ ∀ (r : Run P) (i : P),
      r.Alive i (r.faulty.card / k + 1) → DecidesBy (optmin k) r i (r.faulty.card / k + 1) :=
  ⟨optmin_solves hk, optmin_decidesBy hk⟩

/-- **Lemma 10, as stated, is false.** There is a protocol solving 2-set consensus with `t = 1`
(`n = 6`, inputs `{0, 1, 2}`) in which every low process decides by the time it is low, and a run
in which conditions 1–5 of Lemma 10 hold for process `0` at time `1` with `v = 0`, but process `0`
does not decide `0` at time `1`. -/
theorem lemma10_false :
    ∃ Q : Protocol (Fin 6), SolvesSetConsensus 2 1 {0, 1, 2} Q ∧ LowDecides 2 1 {0, 1, 2} Q ∧
      ∃ r : Run (Fin 6), Adm 1 {0, 1, 2} r ∧ Lemma1HypPaper 2 r 0 1 0 ∧ ¬ DecidesAt Q r 0 1 0 :=
  lemma1_paper_false (fun v hv => by interval_cases v <;> simp)

/-- **Lemma 11.** In a `k`-set consensus protocol in which low processes decide by the time they
are low, no (live) process decides while it is high with hidden capacity `≥ k`. -/
theorem lemma11 (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) {Q : Protocol P}
    (hQ : SolvesSetConsensus k t D Q) (hlow : LowDecides k t D Q) {r : Run P} (hr : Adm t D r)
    {x : P} {m : ℕ} (ha : r.Alive x m) (hhigh : ¬ Low k r x m) (hhc : k ≤ hc r x m) :
    Q.dec r x m = none :=
  lemma3 hk hD hQ hlow hr ha hhigh hhc

/-- **Theorem 4.** `Opt_min-k` is an unbeatable `k`-set consensus protocol in `γ_cr`
(`V ⊇ {0, …, k}`). -/
theorem theorem4 (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) :
    Unbeatable k t D (optmin k : Protocol P) := theorem1 hk hD

end Podc.ParetoOptimalConsensus
