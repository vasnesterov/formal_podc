# Multi-Message Broadcast with Abstract MAC Layers and Unreliable Links — PODC 2014

Mohsen Ghaffari, Erez Kantor, Nancy Lynch, Calvin Newport. *Multi-Message Broadcast with Abstract MAC Layers and
Unreliable Links.* PODC 2014. DOI [10.1145/2611462.2611492](https://doi.org/10.1145/2611462.2611492). Formalized
version: arXiv [1405.1671](https://arxiv.org/abs/1405.1671) v1; numbering follows it.

**Verdict: ⚠️ Minor statement issues.** The BMMB results of Section 3 hold. These are correctness (Theorem 3.4), the
`O((D + k) F_ack)` bound for arbitrary `G'` (Theorem 3.1) and the `O(D F_prog + r k F_ack)` bound for an `r`-restricted
`G'` (Theorems 3.2 and 3.16 with Lemmas 3.3–3.15). All are proved with explicit constants. The problems are local and do not affect the theorems:
* the times `t_{d,ℓ}` used by the key lemma are never defined;
* Lemma 3.12, part 5 is off by one `F_ack` (a slip with evident intent: the proof of Lemma 3.14 cites it in the
  correct, weaker form `ℓF_ack ≤ t_{0,ℓ} + F_ack`);
* Theorem 3.16 as stated ("`R_j(t₁) = K` for every node `j`") needs `G` to be connected (implied by its use of the diameter `D`).

The lower bounds (§3.3) and the enhanced-model algorithm (§4) are not formalized.

## Mistakes in the paper

* **The times `t_{d,ℓ}` of §3.2.4 are never defined** (under-specified definition). Lemma 3.12 lists their
  properties and Lemmas 3.13–3.15 use them. Theorem 3.16 only gives `t₁ = (D + (r+1)k − 2) F_prog + r(k−1) F_ack`,
  which suggests `t_{d,ℓ} = (d + (r+1)ℓ − 2) F_prog + r(ℓ−1) F_ack`. For `r > 1` that formula contradicts
  `t_{0,1} = 0`, which Lemma 3.13 states. We use `t_{d,ℓ} = d F_prog + (ℓ−1)((r+1) F_prog + r F_ack)`. It satisfies
  parts 1–4 of Lemma 3.12 and `t_{0,1} = 0`, and `t_{D,k} ≤ t₁`, so Theorem 3.16 follows with the paper's `t₁`.
  (`tdl`, `lemma_3_12_1` … `lemma_3_12_4`)
* **Lemma 3.12, part 5 (`ℓ F_ack ≤ t_{0,ℓ}` for `ℓ > 1`) is false.** It fails for our `t_{d,ℓ}` and for the formula
  read off Theorem 3.16, whenever `F_ack > 2 F_prog`, which is the regime the paper cares about. Example: `r = 1`,
  `ℓ = 2`, `F_prog = 1`, `F_ack = 3` gives `ℓ F_ack = 6 > 5 = t_{0,2}`. This does not depend on how `t_{d,ℓ}` is
  read: *no* definition satisfying part 4 and `t_{D,k} ≤ t₁` (needed to get Theorem 3.16 "directly from Lemma
  3.15") satisfies part 5 in this example, since part 4 gives `t_{0,2} = t_{D,2} − D F_prog ≤ 5`. The statement is
  false but the proof survives: its only use (Lemma 3.14) needs `ℓ F_ack ≤ t_{0,ℓ} + F_ack`, i.e.
  `(ℓ−1) F_ack ≤ t_{0,ℓ}`, which holds for `r ≥ 1`. (`lemma_3_12_5_false`, `lemma_3_12_5_false_any`; repaired:
  `lemma_3_12_5'`)
* **Theorem 3.16 needs a connected `G`.** It claims `R_j(t₁) = K` for every node `j`, with `D` the diameter. The
  problem statement (§2) explicitly does not assume `G` connected. Then a message only reaches its source's
  component, and the claim fails for two isolated nodes with one message each. Degenerate case. We prove the
  per-component statement and the paper's statement for connected `G`. (`theorem_3_16`, `theorem_3_16_connected`)
* **The MMB specification of §3.2.2 is inconsistent with §2 in the same way.** Part (a) asks every process to deliver
  every message, but §2 asks only for the source's component. We use the component version. (`SolvesMMB`)
* **Theorem 3.2's `O(D F_prog + r k F_ack)` does not follow from `t₁` alone.** `t₁` contains `(r+1) k F_prog`, which is
  `O(r k F_ack)` only if `F_prog = O(F_ack)`. The model never assumes this ("we think of `F_prog` as smaller"). The
  theorem is still true without it: if `F_prog > F_ack`, Theorem 3.1 gives `(D + k) F_ack ≤ D F_prog + k F_ack`. We
  prove `D F_prog + 3 r k F_ack` in all cases. (`theorem_3_2`)
* **Proof gap in the lower bound (§3.3, Lemma 3.20); not formalized.** The model allows a constant number `c` of
  MMB messages per local broadcast (§2: "only a constant number of these messages can fit into a single local
  broadcast message"). In the delay schedule, `b_{i+1}` receives `a_i`'s `m₀`-broadcast over a `G'`
  edge. With `c ≥ 2`, `b_{i+1}`'s later broadcast "containing `m₁`" may also carry `m₀`. The schedule delivers that
  broadcast to `a_{i+2}` over a `G'` edge, so `m₀` jumps ahead and the frontier no longer advances one hop per
  `F_ack`. Against "always send everything you know" the schedule only costs `O(F_ack + D F_prog)`. The argument as
  written covers `c = 1`. We did not determine whether Theorem 3.17 holds for `c ≥ 2`.
* Typos and small slips:
  * Corollary 3.8, proof: "`|R_i(t + F_ack)| ≥ |R_i(t)| + 1`" should be `C_i`.
  * Lemma 3.15, Case 1: "`m′ ∈ R_{j″}(t*) \ C_{j″}(t*)`" should be `R_{j*}(t*) \ C_{j*}(t*)`.
  * Lemma 3.15, Case 2: "by Part 1 of Lemma 3.15" should be "of Lemma 3.5".
  * §3.2: `N^r_G(j)` is defined with "`≤ z`"; "`G′` is a subgraph of `G` (denoted `G ⊆ G′`)" has the roles swapped.
  * Theorem 3.1, proof: the base case "`h = 0`" cannot occur for `ℓ ≥ 1`. The induction should start from the
    trivial case `ℓ = 0`.
  * Lemma 3.11: choosing a *closest* `j″` is unnecessary.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *System.* The composition "BMMB + standard abstract MAC layer" is one event-driven transition system
  (`Model.lean`). A node's state is its `log`, the messages it got in order: `rcvd`, and the order of
  `bcastq`. It also holds the number `acks` of acknowledged broadcasts. The queue is `log.drop acks`, and its head is
  the message currently being broadcast (zero-delay `bcast`). The paper's sets are `R_i = log` and
  `C_i = log.take acks`.
* *Events.*
  * `arrive i m` is the environment's input, at any time.
  * `rcv u v` goes only over `G'` edges, at most once per instance: receive correctness. An instance is a pair
    (sender, message), since BMMB broadcasts each message once.
  * `ack u` happens only after all `G`-neighbours received: acknowledgment correctness.
  * Disabled events are no-ops.
* *Topology.* `G ≤ G'` is a hypothesis where needed. There are no aborts and no crashes. The model is deterministic;
  the adversary picks the event sequence and the times.
* *Time.* Event `n` happens at real time `T (n+1)`, with `T 0 = 0`, `T` monotone and diverging (admissible
  executions). The final state at time `t` is `cfg (last t)`.
* *Bounds.*
  * `AckBound F_ack`: every broadcast is acknowledged within `F_ack` of its `bcast`.
  * `ProgBound F_prog`: the paper's progress bound, with its `connect`/`contend` sets, for closed fragments from the
    final state at `t` to the final state at `t' > t + F_prog`. These are the only fragments the proofs use. Requiring
    fewer fragments makes the hypothesis weaker and the theorems stronger.
* *Arrivals.* The time bounds assume all arrivals happen at time `0`, as the paper does. `k` bounds the set `K` of
  arriving messages.

**Main results in Lean.** Namespace `Podc.MultiMessageBroadcastMAC` (`Exec.` for statements about an execution `α`).

| Paper | Lean | File |
|---|---|---|
| Lemma 3.3 | `Exec.lemma_3_3` | `Lemmas.lean` |
| Lemma 3.5 (1–3) | `Exec.lemma_3_5_1`, `Exec.lemma_3_5_2`, `Exec.lemma_3_5_3` | `Lemmas.lean` |
| Lemma 3.6 | `Exec.lemma_3_6` | `Lemmas.lean` |
| Lemma 3.7 (1–3) | `Exec.lemma_3_7_1`, `Exec.lemma_3_7_2`, `Exec.lemma_3_7_3` | `Lemmas.lean` |
| Corollary 3.8 | `Exec.corollary_3_8` | `Lemmas.lean` |
| Lemma 3.9, Lemma 3.10 | `Exec.lemma_3_9`, `Exec.lemma_3_10` | `Lemmas.lean` |
| Theorem 3.1 | `Exec.theorem_3_1` (bound `(d_G(u,v) + k) F_ack`), `Exec.theorem_3_1_diam`; key claim `Exec.theorem_3_1_key` | `Arbitrary.lean` |
| Theorem 3.4 | `Exec.theorem_3_4` (spec `Exec.SolvesMMB`) | `Correctness.lean` |
| Lemma 3.11 | `Exec.lemma_3_11` | `Restricted.lean` |
| Lemma 3.12 | `lemma_3_12_1` … `lemma_3_12_4`, `lemma_3_12_5'`; `lemma_3_12_5_false`, `lemma_3_12_5_false_any` | `Restricted.lean` |
| Lemmas 3.13, 3.14, 3.15 | `Exec.lemma_3_13`, `Exec.lemma_3_14`, `Exec.lemma_3_15` | `Restricted.lean` |
| Theorem 3.16 | `Exec.theorem_3_16`, `Exec.theorem_3_16_connected` | `Restricted.lean` |
| Theorem 3.2 | `Exec.theorem_3_2` (bound `D F_prog + 3 r k F_ack`) | `Restricted.lean` |

Hypotheses actually needed:
* Theorem 3.4 needs only `AckBound`. It needs nothing about `G'` and no progress bound.
* Theorem 3.1 also needs `F_ack ≥ 0` and all arrivals at time `0`. It does not need `G ≤ G'` or `F_prog`.
* Lemmas 3.9, 3.10 and the `r`-restricted results also need `G ≤ G'`, `ProgBound`, `r ≥ 1` and `F_prog ≥ 0`.

**Not formalized.**
* §3.3: the lower bounds Theorem 3.17 and Lemmas 3.18–3.20. These need a model of arbitrary, randomized algorithms
  and the grey-zone geometry; see the gap noted above.
* §4: the enhanced model and FMMB.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Non-vacuity (`NonVacuity.lean`):
* `ackBound_of_quiescent` and `progBound_of_quiescent` show that executions which finish at time `0` satisfy both
  bounds.
* `Example.example3_nonvacuous` is a concrete execution on the path `0 — 1 — 2` with the unreliable link `0 ⋯ 2`,
  which is 2-restricted. Node 2 first gets `m` over the unreliable link. The execution satisfies every hypothesis of
  Theorems 3.1, 3.2, 3.4 and 3.16, and Theorem 3.2 applies to it.

The model is paper-specific (BMMB's state is built in). It does not reuse `Podc/.../AbstractMAC/`, which has no
unreliable links and no progress bound. Generic pieces such as the final state at time `t` (`Exec.last`,
`exists_gt_last_eq`) could be upstreamed if a generic timed abstract MAC model with `G'` is added to CSLib.
