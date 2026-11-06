# Improved Tradeoffs for Leader Election — PODC 2023

Shay Kutten, Peter Robinson, Ming Ming Tan, Xianbin Zhu. *Improved Tradeoffs for Leader Election.* PODC 2023.
DOI [10.1145/3583668.3594576](https://doi.org/10.1145/3583668.3594576). Formalized version: arXiv 2301.08235v4.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The tradeoff `Ω(log n/(log f(n)+1))` of the abstract, Theorem 3.11 (`Ω(n log n)` messages
for time-bounded algorithms, with explicit bound `(n/2) log₂ n`) and the algorithms of Theorems 3.10 and 3.15 (with
explicit constants) hold after local changes. Theorem 3.8 is one round too strong, and its `k`-round message bound is
only proved as `Ω(n^{1+1/k})`. The Las Vegas, adversarial wake-up and asynchronous results were not checked.

## Mistakes in the paper

### ⚠️ Theorem 3.8 (the `+ 1` and the "consequently" clause on `k`-round algorithms)
Theorem 3.8 is off by one round: with `f(n) = n`, the one-round algorithm in which every node sends its ID to
everybody and the maximum ID wins sends `n(n − 1) ≤ n·f(n)` messages, but the claimed bound
`T(n) > (log₂ n − 1)/(log₂ f(n) + 1) + 1` exceeds 1 for every power of two `n ≥ 2` (`theorem_3_8_as_stated_false`).

**Impact.** The proof gives the bound without the `+ 1` (`theorem_3_8_corrected`). Only the one-round case is
refuted; for `T ≥ 2` the stated bound is unproved. The claim that `k`-round algorithms need `Ω((n/2)^{1+1/(k−1)})`
messages rests on the false bound and is unestablished, not refuted: whether the stronger exponent holds is open. The
corrected bound only gives `Ω(n^{1+1/k})` (`rounds_messages_tradeoff`). That bound (e.g. `Ω(n^{3/2})` instead of
`Ω(n²)` for 2 rounds) still improves polynomially on Afek–Gafni, but no longer matches the `O(n^{3/2})` 3-round
algorithm of Theorem 3.10.

**Details.** The paper claims: at most `n·f(n)` messages imply `T(n) > (log₂ n − 1)/(log₂ f(n) + 1) + 1`. The
broadcast algorithm runs in `T = 1` round, for every ID universe, while with `f(n) = n` the claimed bound is
`(log₂ n − 1)/(log₂ n + 1) + 1 > 1`. The cause is an index slip. The communication graph
`G_r` only contains messages of rounds `< r`, but the proof applies Lemma 3.9 with `r = T`, so the messages of the
last round are never accounted for. The induction step of Lemma 3.9 also builds `G_{r+1}` from the messages "sent
during round `r+1`".

**Repair.** Running the induction one round further gives the corrected bound `T > (log₂ n − 1)/(⌈log₂ f⌉ + 1)`,
in fact `log₂ n ≤ (⌈log₂ f⌉ + 1)·T`. (`theorem_3_8_corrected`)

### 🔧 Theorem 3.8 (`log₂ f` vs. `⌈log₂ f⌉`)
Theorem 3.8 is stated with `log₂ f(n)`, but the proof uses blocks of size `2^{(⌈log₂ f⌉+1)(r−1)}`, and its last
inequality, `2^{σ_T} ≤ 2^{(log₂ f + 1)(T − 1)}`, goes the wrong way when `f` is not a power of two.

**Impact.** The printed form is unproved, not refuted, when `f` is not a power of two; the tradeoff
`Ω(log n/(log f + 1))` is unaffected.

**Repair.** We prove the version with `⌈log₂ f⌉`. (`theorem_3_8_corrected`)

### 🔧 Definition 3.5, Lemma 3.6, Corollary 3.7 (terminating components)
Definition 3.5 ("in **every** restricted prefix `E ∈ Exec_r(X)` all nodes of `X` have terminated") holds vacuously
when `Exec_r(X)` is empty, so Lemma 3.6 fails already for `n = 2` with three singletons, and so does Corollary 3.7
(`lemma_3_6_literal_false`).

**Impact.** The definition must be read existentially. The proof of Lemma 3.6 uses that reading, under which both
results hold and suffice for Theorems 3.8 and 3.11 (`not_disjoint_isolable`, `exists_universe_no_isolable_pow`).

**Details.** The full definition reads "`X` forms terminating components if, for some `r`, in every restricted
prefix `E ∈ Exec_r(X)` all nodes of `X` have terminated". `Exec_r(X)` is empty when some node of `X` must send on
more than `|X| − 1` ports. For the broadcast algorithm every set of fewer than `n` IDs is then "terminating". Lemma
3.6 claims at most `n/2^ℓ` disjoint terminating `2^ℓ`-sets. The proof of Lemma 3.6 actually uses the existential
reading: *some* isolated execution of `X` exists.

### 🔧 Algorithm 1 (Theorem 3.15, nodes must stop)
Algorithm 1 must stop nodes after they select a leader; otherwise later ID blocks keep broadcasting and the
message bound fails.

**Impact.** A missing case in the pseudocode; with it the result holds, with explicit constants
(`SmallIds.electsBy`, `SmallIds.terminatesBy`, `SmallIds.msgBound`).

**Details.** The assumption `d ≤ n` is not needed.

### 🔧 Lemma 3.14 (quantifiers)
"Every execution prefix in `Exec_{r_i}(I)`" is stronger than what the construction provides, since the round `r_I`
depends on the chosen execution.

**Impact.** One adversarial execution per set suffices for Lemma 3.13 (`level_step`).

### ✏️ Slips
- Algorithm 1 for `n = 1`: the rule "select when receiving messages" never fires (`SmallIds.electsBy`).
- Theorems 3.11 and 3.13 drop the `n log₂ n` IDs that Corollary 3.7 removes: Lemma 3.14 needs
  `n T'^{log₂ n − 1} + n log₂ n` IDs for the single-send algorithm, whose time is `T' = nT` (Lemma 3.12). We prove
  Theorem 3.11 with `n log₂ n + n^{log₂ n} T^{log₂ n − 1}` IDs (`theorem_3_11`).

## Proof gaps (statements true)

### 🔧 Lemma 3.14 (merging)
The merging step wires the two clusters by independent maps `g`, `h`, so a node can receive two new links and keep
capacity `2^i − 2`, not the claimed `|D|/2 − 1`.

**Impact.** Property (a) does not follow from the printed construction; the lemma holds with a different wiring
(`merge`).

**Details.** The ports opened by `C` are wired into `C'` by an arbitrary one-to-one map `g`, and those opened by `C'`
into `C` by an independent `h`.

**Repair.** Wiring along one perfect matching `C ↔ C'`. (`merge`)

### 🔧 Lemma 3.14 (counting)
"`U_i` contains many pairwise disjoint sets" is not preserved by `|U_i'| ≥ |U_i|/T`.

**Impact.** Property (c) does not follow as printed (`level_step`).

**Repair.** The pigeonhole must be applied to a disjoint subfamily. (`level_step`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Proof remarks.** Theorem 3.10: up to `n^{1/(k−1)}` survivors can remain after the last two-round iteration, and
the final all-to-all round selects the maximum; its cost is within the claimed bound. The referee counts
`⌈n^{i/(k−1)}⌉` can exceed `n − 1` for small `n`, so the algorithm caps them. Lemma 3.14, absorbing phase: how the
first `|C|/2 − 1` new ports are kept inside `C` is left implicit; we track capacity per node (`absorb`).

**Model.** (`Model.lean`)
- Synchronous clique of `n = m + 1` nodes, KT0: a node initially knows only its ID and `n`. Each node has `m`
  ports, and the adversary chooses the port mapping (`IsPortMap`: per node a bijection of ports onto the other
  nodes). Nodes are identified with their IDs, and the ID assignment `I` is an `n`-subset of the ID universe `U`.
- Deterministic algorithms (`Algorithm m`): the initial state depends on the own ID; in each round a node sends
  at most one message per port, computed from its state; LOCAL (unbounded messages); simultaneous wake-up.
- Executions are also defined for *partial* port mappings (`run`, `Valid`). These are the paper's restricted
  execution prefixes. Any compatible full port mapping yields the same prefix (`run_eq_of_extends`), which
  formalizes the adversary wiring unused ports adaptively (`augment`).
- Lower bounds assume only `ElectsBy A U T`: in every execution, after round `T` exactly one node outputs
  "leader". This is weaker than termination with irrevocable outputs, so the lower bounds are stronger. Message
  bounds count rounds `1..T` (`MsgBound`). Upper bounds additionally prove `TerminatesBy`: every node decides by
  round `T`, never changes its output and stays silent afterwards.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.6 (existential reading) | `not_disjoint_isolable` | `Isolation.lean` |
| Corollary 3.7 (existential reading) | `exists_universe_no_isolable`, `exists_universe_no_isolable_pow` | `Isolation.lean` |
| Lemma 3.9 + Claim 1 (one round further) | `good_zero`, `good_step` | `Tradeoff.lean` |
| Theorem 3.8, corrected | `theorem_3_8_corrected` (core: `tradeoff_lower_bound`) | `Tradeoff.lean` |
| Theorem 3.8, "consequently", corrected | `rounds_messages_tradeoff` | `Tradeoff.lean` |
| Theorem 3.8 as stated is false | `theorem_3_8_as_stated_false` | `Counterexamples.lean` |
| Definition 3.5 / Lemma 3.6 literal is false | `terminatingLiteral_broadcast`, `lemma_3_6_literal_false` | `Counterexamples.lean` |
| Lemma 3.12 (single-send simulation) | `lemma_3_12`, `msgs_simulate`, `electsBy_simulate` | `SingleSend.lean` |
| Lemma 3.14 (absorbing, merging) | `absorb`, `merge`, `level_step` | `MessageLB.lean`, `NLogN.lean` |
| Lemma 3.13 | `single_send_lower_bound` | `NLogN.lean` |
| Theorem 3.11 | `theorem_3_11` | `NLogN.lean` |
| Theorem 3.10 (improved Afek–Gafni, `ℓ` odd) | `Referees.theorem_3_10` (generic: `Referees.electsBy`, `Referees.msgs_le`) | `Referees.lean` |
| Theorem 3.15 (Algorithm 1, small ID universes) | `SmallIds.selects_min`, `SmallIds.electsBy`, `SmallIds.terminatesBy`, `SmallIds.msgBound` | `SmallIds.lean` |

**Not formalized.** Theorem 3.16 (Las Vegas algorithms), Section 4 (adversarial wake-up, randomized lower bound
Theorem 4.2) and Section 5 (asynchronous algorithms). All of them involve randomization or asynchrony.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity: the broadcast algorithm (`broadcast_electsBy`, `broadcast_terminatesBy`, `broadcast_msgBound`)
satisfies the hypotheses of the lower bounds for every ID universe. It terminates in one round with irrevocable
outputs, so the counterexamples refute the paper's statements in its own correctness notion, not only the weaker
`ElectsBy`. The upper bounds are proved for every ID assignment and every port map. Theorem 3.10: for `ℓ = 2K + 1` rounds and referee counts `⌈n^{i/(K+1)}⌉`, the algorithm elects the maximum and sends at most `4(ℓ + 1)·n^{1 + 2/(ℓ+1)}` messages. Theorem 3.15: IDs in `[1, n·g]`; it elects the minimum, which every node learns, within `⌈n/d⌉` rounds and with at most `(n − 1)·d·g` messages. The model is self-contained in this folder: no CSLib model of
KT0 cliques with port numbers exists. CSLib candidates: `Model.lean`, `Glue.lean`, `Isolation.lean`,
`SingleSend.lean` (the generic part: partial port maps, adaptive wiring, gluing, single-send simulation).
