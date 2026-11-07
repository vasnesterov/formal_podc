# Uniform Deployment of Mobile Agents in Asynchronous Rings — PODC 2016

Masahiro Shibata, Toshiya Mega, Fukuhito Ooshita, Hirotsugu Kakugawa, Toshimitsu Masuzawa. *Uniform Deployment
of Mobile Agents in Asynchronous Rings.* PODC 2016. DOI
[10.1145/2933057.2933093](https://doi.org/10.1145/2933057.2933093). Formalized version: the journal version (JPDC
119:92–106, 2018), accepted manuscript from the Kyutech repository (record 6499), which contains the full proofs.
Numbering follows it.

**Verdict: ✏️ Slip.** All checked results hold:
- Algorithm 1 is correct, including periodic rings and `n ≠ ck` (Theorem 3).
- Uniform deployment with termination detection is impossible without knowledge of `k` or `n` (Theorem 5).
- The combinatorial lemmas behind Algorithm 4 hold (Lemmas 2–4).
- The `Ω(kn)` lower bound on moves holds (Theorem 1), with constant `1/6` instead of `1/16` when `k ≤ n/4`, and for
  every `p < 1` once `n ≥ 2/(1−p)`.

The mistakes are slips in the pseudocode of Algorithms 2 and 6, and the intended versions behave correctly in our
simulations. The correctness of Algorithms 2–3 (Theorem 4) and 4–6 (Theorem 6) is not proved in Lean.

## Mistakes in the paper

### ✏️ Slips
- **Algorithm 2 / Section 3.2.** The loop `while phase ≠ ⌈log k⌉` (with `phase = 1`) runs only `⌈log k⌉ − 1`
  sub-phases and never makes the last active agents leaders. For `k = 2` it does nothing at all. Also, "at most
  `⌈log k⌉` sub-phases" is off by one: with `k = 2` and an asymmetric placement, the surviving agent becomes a
  leader only in sub-phase 2. The bound is `⌊log₂ k⌋ + 1`. Looping until lines 6, 15 or 16 fire is clearly intended,
  and `O(n log k)` is unaffected.
- **Algorithm 6, line 14.** `D_ℓ` has `4k'_ℓ` entries, but the test may need `D_ℓ[j + t]` and
  `D_ℓ[0] + … + D_ℓ[t−1] = nodes_ℓ − nodes` beyond that range. Read with in-range indices, a misestimating agent
  can reject every correct message. On the aperiodic ring with distances `(1,1,9,9,9,9,1,2,2,1,1)` (`n = 45`,
  `k = 11`), our simulator finds a fair execution in which all agents stay suspended forever without uniform
  deployment. Reading `D_ℓ` cyclically, as the text ("memorizes `a_i`'s whole distance sequence as a part of
  `D_ℓ`") and the proof of Lemma 5 require, fixes it. Simulation only.
- **Proof of Theorem 5.** The claim that the agents `a'_0, …, a'_{k−1}` of the large ring behave like `a_0, …,
  a_{k−1}` is unjustified, and can fail, since they start next to the empty half of `R'`. The proof actually uses
  Lemma 1 on the last copy `V*`, which is correct (`theorem_5`).

### Typos
- Section 3.2 says the selection phase of Algorithm 1 needs `O(n log k)` space; it is `O(k log n)`.
- Section 3.1 bounds `rank ≤ k′ − 1` with `k'` undefined; in fact `rank` is smaller than the minimal period of `D`.
- PODC 2016 was the 35th symposium, not the 29th (footnote I).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`, Section 2.1).
- Asynchronous unidirectional ring `ZMod n`; each node has a token counter, the agents staying on it, and a FIFO
  incoming queue.
- Agents are anonymous deterministic state machines. In one atomic action an agent consumes its messages, reads the
  token count and the states of the co-located staying agents, may release a token, may broadcast one message to the
  co-located agents, and stays or leaves.
- The adversary is the schedule: an infinite sequence of agents, fair if each agent appears infinitely often.
  Scheduling an agent that cannot act is a no-op.
- No faults, no randomness.
- Initially every agent sits in the incoming buffer of its home node, as the paper assumes.
- Two powers exceed the paper's: agents see co-located states, and token releases are unrestricted. Both only
  strengthen Theorem 5, and Algorithm 1 uses neither.
- Definition 1 is `SolvesTD`: in every fair execution all agents halt, and when all have halted no agent is in
  transit and the deployment is uniform (`IsUniform`: distinct nodes, gaps `⌊n/k⌋` or `⌈n/k⌉`).
- "Knowledge of `k`" means the algorithm is a family `alg1 k`. "No knowledge" means one algorithm for all rings.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (`Ω(kn)` moves; combinatorial form, see below) | `theorem_1` (`kn ≤ 6·moves`, `4k ≤ n`), `theorem_1_tight`, `theorem_1_of_le_mul` (any `p < 1`) | `LowerBound.lean` |
| Theorem 3, correctness (Algorithm 1 + §3.1.1) | `theorem_3` | `Alg1.lean` |
| Theorem 3, moves (`n + moves1 D < 3n` per agent) | `alg1_moves_lt`, `trajMove_eq` | `Alg1.lean` |
| Targets of Algorithm 1 are distinct and uniform | `alg1_targets` | `Alg1Targets.lean` |
| Theorem 5 (impossibility without knowledge) | `theorem_5` | `Impossibility.lean` |
| Lemma 1 (replication, asynchronous version) | `replay_step`, `replay` | `Impossibility.lean` |
| Lemma 2 | `lemma_2`, `lemma_2_fun` | `Words.lean` |
| Lemma 3 | `lemma_3`, `lemma_3_card` | `Words.lean` |
| Lemma 4 | `lemma_4`, `lemma_4_sum` | `Words.lean` |

**How the proofs go.**
- **Theorem 3.** The paper calls correctness "obvious". Our proof makes the omitted points explicit: a walking agent
  always finds the token of every home node it passes (incoming buffers and FIFO links); targets are distinct and
  uniform also for periodic rings and `n ≠ ck`; every agent terminates under every fair schedule. The proof follows
  each agent along its schedule-independent trajectory (`traj`). A global invariant (`Inv`) tracks positions, tokens,
  and "an agent that has not acted yet heads its home queue". The potential (remaining actions) decreases under fair
  schedules.
- **Theorem 5** replays the round-robin execution of the 2-node ring at every corresponding node of a window of the
  big ring. The window shrinks by one node per atomic step.
- **Lemma 4** is proved via a weak Fine–Wilf lemma (`HasPeriodOn.gcd`).

**Not formalized.**
- In Theorem 1, the step "an agent moving from `h` to `t` makes at least `(t − h).val` moves" is not derived
  in the execution model; the Lean statement bounds the total forward distance from the block start `0, …, k−1`
  to any uniform final placement.
- Theorem 2.
- Ideal time and memory bounds.
- Theorem 4 (Algorithms 2–3).
- Theorem 6 with Lemmas 5–9 (Algorithms 4–6).

`tools/` contains a Python simulator of the model with Algorithms 1–6. With the loop guard of Algorithm 2 fixed and
the cyclic reading of Algorithm 6, it found no failure in thousands of random and adversarial fair schedules
(`test1.py`, `test23.py`, `burst.py`); `target456.py` reproduces the literal-reading failure of Algorithm 6.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
problem definition is not vacuous: `theorem_3` exhibits an algorithm (with knowledge of `k`) that satisfies
`SolvesTD` in every ring. The model is paper-local (CSLib candidate).
