# How to Tame Multiple Spending in Decentralized Cryptocurrencies — PODC 2022

João Paulo Bezerra, Petr Kuznetsov. *Brief Announcement: How to Tame Multiple Spending in
Decentralized Cryptocurrencies.* PODC 2022. DOI
[10.1145/3519270.3538465](https://doi.org/10.1145/3519270.3538465). Formalized version: the full
version, arXiv [2205.14076](https://arxiv.org/abs/2205.14076) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** The lower bound (Theorem 5.1: no `k`-Consistent Broadcast
for `k` below the inconsistency number `k_max`), and with it the advertised "the optimal spending
number is precisely the inconsistency number", is false: we give trust models with `k_max = 3`
and `k_max = 2` where `2`-CB, resp. `1`-CB, is implementable (for every source, with per-value
Local Progress). The correct optimum for a source `s` is `max(1, λ_s)`, the maximum restricted to
faulty sets containing `s`; we prove both bounds. Theorem 3.6 (uniform model, with the implicit
`f < q ≤ n`), Theorem 4.1, Lemmas 4.3–4.7 and Theorem 4.8 (Algorithms 1–2 implement
`k_max`-spending asset transfer, safety and liveness) hold, the latter with assumptions on the
correct issuers that the paper uses implicitly.

## Mistakes in the paper

* **Theorem 5.1 is false (headline).** The proof lets a Byzantine source `r ∈ F` equivocate to the
  members of an independent set of a graph `G_{F,S}` with maximum independence number. But the
  maximum may be attained only by faulty sets that do *not* contain the source — typically
  `F = ∅`, when correct processes have disjoint quorums. With a correct source nothing can go
  wrong, and with a faulty source the relevant graphs have smaller independence number.
  Smallest example: three processes, each process's only quorum is itself, at most one failure
  (the uniform model with `q = 1`, `f = 1`). With no failures all three processes are pairwise
  independent, so `k_max = 3`. But "the source sends its value, every process delivers the first
  value it gets from the source" is a `2`-CB for every choice of source: with a correct source
  only one value is delivered, with a faulty source only two processes are correct
  (`theorem_5_1_false`). A less degenerate example has four processes `a, a', b, b'` with
  quorums `{a,a'}`, `{b,b'}`, `Π`, `Π` and faulty sets `∅, {a}, {b}`: `k_max = 2`, yet a
  quorum-echo algorithm is a `1`-CB for every source (`theorem_5_1_false'`).
  **Repaired statement.** With `λ_s` the largest independence number of the graphs `G_{F,S}`
  with `s ∈ F`, every `k`-CB with (per-value) Local Progress has `k ≥ λ_s` (`lower_bound`,
  `srcInconsistencyNumber_le`, the paper's gluing argument; it uses `∅ ∈ F`, which follows from the
  standing inclusion-closure assumption), and the quorum-echo algorithm achieves `max(1, λ_s)`
  (`echoAlg_isKCB`). So the optimal `k` is `max(1, λ_s)`, not `k_max` (`optimal_kcb`).
* **Local Progress is too weak for the proof of Theorem 5.1.** The proof needs Local-Progress
  executions in which the `k` processes deliver `k` *different* values, but Local Progress only
  promises that `p` delivers *some* value. With three processes `s, a, b`, quorums `Π`, `{s,a}`,
  `{s,b}` and faulty sets `∅, {s}`, the source is faulty in the only graph attaining
  `k_max = λ_s = 2`; still, an algorithm in which `a` and `b` deliver a default value on their
  own, and any other value only when both echoed it, satisfies Local Progress and is a `1`-CB
  (`WeakLP.theorem_5_1_needs_localProgressAll`). Per-value Local Progress, which the proof
  evidently intends, fixes this.
* **"Algorithms 1 and 2 implement k-SAT with optimal k" (end of §5)** fails for the same reason;
  in fact the paper's own algorithm can beat `k_max`. Only faulty issuers spend an input twice,
  and a faulty issuer spends it at most `λ(Q, {B})` times, `B` the actual faulty set
  (`spendingNumber_le_refined`). In the three-process example above (`k_max = 3`) every run of
  Algorithms 1–2 has spending number at most `2` (`algorithms_beat_kmax`); in the four-process
  example (`k_max = 2`) nothing is ever spent twice (`algorithms_no_double_spending_pairsT`).
* **Theorem 3.6 needs `f < q ≤ n`** (not stated). For `q ≤ f` the formula's denominator is `≤ 0`;
  the inconsistency number is then `n − q + 1` (`theorem_3_6_needs_q_gt_f`). The proof also only
  handles faulty sets of size exactly `f` and never shows that `⌊(n−f)/(q−f)⌋` is attained; both
  are easy and added (`inconsistencyNumber_uniform` gives the value for all `f`).
* **Smaller slips.** Accuracy says verify-acc returns true "iff `AC ⊆ F`"; the "if" direction is
  impossible for a run-independent function (`Setup.accuracy_iff_impossible`), "only if" is meant. The
  proof of Lemma 4.4 does not say why the `k` acceptors are distinct (No-Conflict of each history).
  Example 3.1 writes the fault model `{{p₃}}` (not inclusion-closed) and gives `p₃` a quorum without
  `p₃`. Algorithm 1 line 5 checks the REQ signature against the sender instead of the issuer, and
  line 26 omits `tx ≠ tx'`. Theorem 5.2's proof writes `deliver(m)` for a transaction carrying `m'`.
  Validity (Lemma 4.7) silently assumes that a correct process issues only valid transactions whose
  inputs it has already accepted and never issues conflicting ones; `transfer` checks neither.
  Without the input condition Validity fails (`ValidityCex.validity_needs_inputs`).

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* Trust model `(Q, F)`: a quorum map and a fault model over a finite process set; `p ∈ Q` for every
  quorum of `p` (`SelfMem`), `F` inclusion-closed (`DownClosed`) and every process has a quorum
  (`HasQuorums`) are explicit hypotheses where used. `G_{F,S}` is a Mathlib `SimpleGraph` on the
  correct processes; independence number = `SimpleGraph.indepNum`.
* Asset transfer (§4): transactions are an abstract type with issuer, output map and input set.
  Algorithms 1–2 run in an asynchronous interleaving model with a static Byzantine set `B ∈ F`,
  authenticated channels (messages may be received any number of times), unforgeable issuer
  signatures (Byzantine processes inject only correctly signed content), and liberal guards (a
  superset of the code's behaviours). Correct processes never issue conflicting transactions
  (`HonestIssuers`) where needed, as the paper assumes implicitly. Liveness is over infinite
  executions with reliable delivery between correct processes and weak fairness of every action
  (`Setup.Exec.Fair`); fair executions exist (`Setup.exists_fair`).
* `k`-CB (§5): the asynchronous Byzantine broadcast model `Cslib.Byzantine.AsyncBroadcast`
  (staged in `Podc/`) with adaptive corruption, weak fairness for liveness, and executions whose
  set of corrupted processes lies in `F`. Delivery is the single decision. Algorithms are arbitrary
  guard-based protocols (guards may read everything a process received and sent).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 3.4 (inconsistency number) | `inconsistencyNumber` | `Trust.lean` |
| Example 3.5 (`λ = 2`) | `example_3_5`, `example_3_5_literal` | `Examples.lean` |
| Theorem 3.6 (with `f < q ≤ n`) | `theorem_3_6`; all `f`: `inconsistencyNumber_uniform` | `Uniform.lean` |
| Theorem 3.6 for `q ≤ f`: formula fails | `theorem_3_6_needs_q_gt_f` | `Uniform.lean` |
| Table 1 (Example 3.7) | `table_1` | `Uniform.lean` |
| Theorem 4.1 | `TxSystem.theorem_4_1` | `Transactions.lean` |
| Lemma 4.3 | `Setup.lemma_4_3` | `Safety.lean` |
| Lemma 4.4 (`k_max`-Spending) | `Setup.lemma_4_4`; sharper: `Setup.spendingNumber_le_refined` | `Safety.lean` |
| Theorem 4.8: Integrity, Accuracy, Monotonicity | `Setup.integrity`, `Setup.accused_byzantine`, `Setup.hist_mono`, `Setup.acHist_mono` | `Safety.lean` |
| Lemma 4.5 (Eventual Conviction) | `Setup.lemma_4_5`, `Setup.conviction` | `Liveness.lean` |
| Lemma 4.6 (Termination) | `Setup.lemma_4_6` | `Liveness.lean` |
| Lemma 4.7 (Validity, with implicit assumptions) | `Setup.lemma_4_7`, `Setup.lemma_4_7_of_issue` | `Liveness.lean` |
| Lemma 4.7 without "issuer accepted the inputs": fails | `ValidityCex.validity_needs_inputs` | `Liveness.lean` |
| Theorem 4.8: Agreement | `Setup.agreement` | `Liveness.lean` |
| Theorem 5.1: **false** | `theorem_5_1_false`, `theorem_5_1_false'` | `Broadcast.lean`, `EchoBroadcast.lean` |
| Theorem 5.1 repaired (lower bound `λ_s`) | `lower_bound`, `srcInconsistencyNumber_le` | `LowerBound.lean` |
| Corrected §5: optimal `k = max(1, λ_s)` | `optimal_kcb` | `Main.lean` |
| Matching upper bound `max(1, λ_s)` | `echoAlg_isKCB`, `echoAlg_localProgressAll` | `EchoBroadcast.lean` |
| Theorem 5.1 needs per-value Local Progress | `WeakLP.theorem_5_1_needs_localProgressAll` | `WeakLocalProgress.lean` |
| Optimality of Algorithms 1–2 (end of §5): **false** | `algorithms_beat_kmax`, `algorithms_no_double_spending_pairsT` | `Optimality.lean` |

**Not formalized.** Theorem 5.2 (reduction from `k`-CB to `k`-SAT), Section 6 (clusters; no
theorem there).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexample algorithms are proved to satisfy the full `k`-CB specification
(Validity in fair executions, `k`-Consistency, Integrity) and Local Progress.
