# Small Buffers on a Path (AQT) — PODC 2019

Avery Miller, Boaz Patt-Shamir, Will Rosenbaum. *With Great Speed Come Small Buffers: Space-Bandwidth Tradeoffs for
Routing.* PODC 2019. DOI [10.1145/3293611.3331614](https://doi.org/10.1145/3293611.3331614). Formalized version:
arXiv [1902.08069](https://arxiv.org/abs/1902.08069) v1 (the only version, with the appendix); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** **Lemma 4.8 is false for HPTS as printed**: Algorithm 3 processes the levels
of a phase in increasing order, while the proof needs decreasing order. We prove Lemma 4.8 and Theorem 4.1 (space
`ℓ n^{1/ℓ} + σ + 1` when `ρℓ ≤ 1`) for **HPTS with the levels of each phase in decreasing order** (a one-line change
to Algorithm 3). Theorem 4.1 claims only that *some* algorithm "HPTS" achieves the bound, so this variant proves it.
**For Algorithm 3 as printed, the bound is unverified (open).** PTS/PPTS on paths and trees (Propositions 3.1, 3.2,
3.5, B.3) and the lower bound (Theorem 5.1) are proved. The proof of Claim 2 is replaced by a new argument, and the
lower bound needed small repairs. The `O(ℓ d^{1/ℓ} + σ)` upper bound of the abstract (in terms of the number `d` of
destinations) is never proved in the paper.

## Mistakes in the paper

* **Lemma 4.8 is false for Algorithm 3 as printed.** Algorithm 3 works at level `λ = t mod ℓ` and accepts new packets
  when `λ = 0`, so a phase runs the levels `0, 1, …, ℓ−1`. The indexing in the statement of Lemma 4.8 (rounds
  `t+1, …, t+ℓ`) gives `1, …, ℓ−1, 0`. The proof assumes the opposite: "levels are activated in decreasing order over
  the course of a phase". In the round of level `λ`, a bad packet can be traded for a bad packet at a lower level
  (Case 2 of Claim 2). If that lower level was already processed in this phase, the badness does not decrease.
  Counterexample (`m = ℓ = 3`, 27 nodes, no injections): node 8 holds two packets to 15, node 9 one packet to 15,
  node 10 two packets to 20 and one packet to 15. Node 10 has badness 1: a bad level-2 packet with intermediate
  destination 18. The rounds at levels 0 and 1 do nothing. At level 2, node 8 sends a packet to its intermediate
  destination 9, where it becomes pre-bad at level 1. `ActivatePreBad` then pushes node 9's level-1 packet into
  node 10, which is busy forwarding at level 2. Node 10's badness stays 1, for both orders `0,1,2` and `1,2,0`.
  Here badness follows Definition 4.5 restricted to intermediate destinations `w_k > i` (see the item on Algorithm 5
  below; the other fix there, to Algorithm 5 line 5, plays no role in this instance). Read
  literally, Definition 4.5 also counts node 8's bad level-2 packet at node 10, although that packet never crosses
  node 10; then node 10's badness drops from 2 to 1 in this instance. But the literal definition breaks the first
  step of the proof of Theorem 4.1, `B(i) ≤ ξ(i) + 1`: with `m ≥ 6`, three packets injected at once at node 0 for
  node 1 (`σ = 2`) give `B(5) = 2` and `ξ(5) = 0`. The restricted definition is the one the proof needs.
  This is a false lemma, and the proof of Theorem 4.1 rests on it. Nothing shows that the theorem itself fails for
  the printed order: random simulations found no violation, and the bound has slack `ℓ`. With levels in decreasing
  order (`ℓ−1, …, 0`) we prove Lemma 4.8 and Theorem 4.1. (`lemma_4_8_false_alg3`, `lemma_4_8_false_indexing`;
  repaired: `lemma_4_8`, `theorem_4_1`)
* **The proof of Claim 2 (badness never increases in a round) is not a proof; the claim is true.** Item 1 should say
  `j > λ`, not `j < λ`. Item 3 is argued through events (a)–(c) and Cases 1–3, which do not account for each unit of
  badness. Our replacement: within a level-`(λ−1)` block, the nodes active at level `λ` form a suffix. A lower-level
  pseudo-buffer can gain a bad packet only at the first node of that suffix. So for every node `i`, the lower levels
  gain at most one unit of badness, and only when `i` is active at level `λ`, where it loses one unit (Lemma 3.4).
  The final step of the proof of Lemma 4.8 ("hence `B^{s+}(i) = B^s(i)`, as desired") is also garbled.
  (`Bad_low_le`, `Bad_lam_le`, `phase_decreasing`)
* **Algorithm 5 (`ActivatePreBad`) and Definition 4.5 are imprecise.** Line 5 should read `i < w_k`. Activating the
  empty pseudo-buffer at `w_k` itself would block the pre-bad run of a packet arriving at `w_k` one level lower. The
  sum in Definition 4.5 must be restricted to intermediate destinations `w_k > i`, as in Definition 3.3. (Formalized
  with both fixes.)
* **The abstract and introduction claim a result the paper never proves.** They state `O(ℓ d^{1/ℓ} + σ)` space for
  `d` destinations, and `O(log d)` space when `ρ ≤ 1/log d`. Theorem 4.1 and its proof are in terms of the number
  `n` of nodes, and the hierarchy is built on node indices, so the `d`-form does not follow directly. Not
  formalized; our sharper form gives only `min(ℓ n^{1/ℓ}, d) + σ + 1`. (The lower bound in terms of `d` follows
  from Theorem 5.1, since `d ≤ n`.)
* **Lower bound (Theorem 5.1): gaps, statement true.** (i) Injecting "`ρm` packets per phase" at once is not
  `(ρ,1)`-bounded; we spread the injections at rate `ρ`. (ii) Lemma 5.4 counts β-stale packets by the load of
  `[F(t+1)+1, F(t)]` in round `t+1`, but such a packet may already be delivered then and occupy no buffer. We count
  them in round `t`. (iii) The construction needs `(ℓ+1)m^ℓ + 1` nodes, not `(ℓ+1)m^ℓ` ("destination `n`"). We prove
  load `≥ ((ℓ+1)ρ−1)(m−1)/(4(ℓ+1)) − 1` against every protocol. With `n ≈ (ℓ+1)m^ℓ`, this is the paper's
  `Ω(((ℓ+1)ρ−1)/ℓ · n^{1/ℓ})` up to constants. Lemma 5.5 is replaced by a global telescoping count.
  (`theorem_5_1`, `exists_load_ge`)
* **Trees (Appendix B.2): badness defined too broadly; statements true.** Definition B.4 / the PPTS-tree badness sums
  `B_k(v)` over *all* destinations. With that definition "`B(v) ≤ ξ(v) + 1`" fails: inject 3 packets at a child of
  `v` with destination `v`; then `ξ(v) = 0` but `B(v) = 2`. Restricting to destinations above `v` (as Definition 3.3
  does on the path) repairs it. Proposition 3.5 also omits `ρ ≤ 1`. (`Tree.prop_3_5`, `Tree.prop_3_5_depth`)
* **Typos and small slips.** Definition 2.1 writes `N_T(v)` for an interval `I`. The proof of Lemma 2.5 writes
  `ℓ·s + 1` for `ℓ(s−1) + 1`. Algorithm 2 line 2 uses an undefined `w_d`. The proof of Theorem 5.1 writes `/2k` for
  `/2ℓ`. The phase boundaries in Section 4.2 (rounds `(φ−1)ℓ … φℓ−1`) and in Lemma 4.8 (`t+1 … t+ℓ`) disagree.
  Section 4.1 says `I_{j,r}` has `m^j` nodes and `I_j = {I_{j,r} : r ∈ ⟨m^j⟩}`, and Algorithm 3 line 6 ranges over
  `r ∈ ⟨m^{ℓ−λ}⟩`; it should be `m^{j+1}` nodes and `r ∈ ⟨m^{ℓ−j−1}⟩` (as in the definition of `I_{j,r}` and in
  Algorithm 5).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous rounds on the directed path `0 → ⋯ → n−1`. Each edge carries one packet per round. A round is an
  injection step followed by a forwarding step, and buffer occupancy is measured between the two. Deterministic and
  centralized, with no failures.
* Adversaries are count functions `A t a b` (round, source, destination), `(ρ,σ)`-bounded on every buffer and every
  interval of rounds (`Cslib.AQT.IsBounded`, staged in `Podc/Computability/Distributed/AQT/Basic.lean`), with real
  `ρ ≥ 0` and `σ`.
* **Upper bounds.** Configurations count the packets per node and destination. HPTS is formalized for `n = m^ℓ`
  (`hptsStep`): FormPaths in closed form (`fpAct`), then `ActivatePreBad` for levels `λ−1, …, 0`. The packet a
  pseudo-buffer sends is chosen arbitrarily (`ValidSel`), so every priority rule is covered. A `Run` uses one level
  per round according to a schedule, and new packets are accepted in batches at phase starts: the `ℓ`-reduction
  `reduce A ℓ`. Pending packets are not counted, as in the paper. PPTS and PTS are HPTS with `ℓ = 1`, `m = n`,
  accepting packets in their injection round.
* **Trees.** A finite forest given by a parent map (`Tree.DTree`). Packets move towards ancestors, and destinations are
  ordered by a topological index. Algorithm 6 is formalized both as the loop and in closed form (`Tree.act`).
* **Lower bound.** Arbitrary offline protocols: any trajectories that move each packet at most one hop per round
  towards its destination, with at most one packet per edge per round (`LowerBound.Execution`). The adversary
  `lbAdv` is a finite packet family.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.3 | `Cslib.AQT.excess_le`, `Cslib.AQT.cross_succ_le` | `Podc/…/AQT/Basic.lean` |
| Lemma 2.5 | `Cslib.AQT.reduce_isBounded` | `Podc/…/AQT/Basic.lean` |
| Lemma 3.4 + Claim 1 / Claim 2 (2) | `Bad_lam_le`, `fpAct_of_Bad_lam_pos` | `RoundMain.lean` |
| Claim 2 (1), (3) | `Bad_high_eq`, `Bad_low_le` (via `fpAct_of_bad_arrival`, `BadArr_unique`) | `RoundMain.lean`, `RoundBad.lean` |
| Algorithm 4 (FormPaths) = our closed form `fpAct` | `fpAct_eq_loop` (loop `loopAct`) | `FormPaths.lean` |
| Lemma 4.7 | by construction (`actLv : ℕ → Option Key`) | `HPTS.lean` |
| Lemma 4.8 (false as printed) | `lemma_4_8_false_alg3`, `lemma_4_8_false_indexing` | `Counterexample.lean` |
| Lemma 4.8 (decreasing levels) | `lemma_4_8`, `phase_decreasing` | `Counterexample.lean`, `Phase.lean` |
| Theorem 4.1 (decreasing levels) | `theorem_4_1` (sharper: `Run.occ_le_keys`, `Run.badness_le`) | `Theorem41.lean` |
| Proposition 3.1 (PTS) | `prop_3_1` | `Corollaries.lean` |
| Proposition 3.2 (PPTS) | `prop_3_2` | `Corollaries.lean` |
| Propositions 3.5, B.3 (trees) | `Tree.prop_3_5`, `Tree.prop_3_5_depth`, `Tree.prop_B_3` (Lemma B.5: `Tree.bad_step_le`; Algorithm 6 loop = closed form: `Tree.alg6_eq_act`) | `Tree.lean` |
| Claim 3, Lemma 5.3 | `LowerBound.claim3`, `LowerBound.lemma_5_3` | `LowerBound.lean` |
| Lemmas 5.2, 5.4 | `becomeStale_pos`, `card_becomeStale_le_one`, `card_becomeStale_le_sum_load`, `lemma_5_4_drop` | `LowerBound.lean` |
| Theorem 5.1 | `LowerBound.theorem_5_1` (sharper: `exists_load_ge`) | `LowerBound.lean` |

`Hierarchy.lean` holds the base-`m` level arithmetic (Definitions 4.2, 4.3).

**Not formalized.** The `d`-destination form of the upper bound from the abstract, and general `n ≠ m^ℓ`.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`; the
counterexample is checked by `decide +kernel`. Non-vacuity: every schedule and adversary has a run with a canonical
packet choice (`canonRun`), executions of any protocol exist (`LowerBound.Execution.idle`), and the lower-bound
adversary is `(ρ,1)`-bounded (`lbAdv_isBounded`). Lean names are in the namespace `Podc.SmallBuffersAQT`.
