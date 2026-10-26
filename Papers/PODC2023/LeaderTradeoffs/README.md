# Improved Tradeoffs for Leader Election — PODC 2023

Shay Kutten, Peter Robinson, Ming Ming Tan, Xianbin Zhu. *Improved Tradeoffs for Leader Election.* PODC 2023.
DOI [10.1145/3583668.3594576](https://doi.org/10.1145/3583668.3594576). Formalized version: arXiv 2301.08235v4.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The two deterministic lower bounds for the synchronous clique with
simultaneous wake-up hold after repairs. Theorem 3.8 (time–message tradeoff) is false as stated, by one round:
a one-round algorithm violates it for every `n`. The proof gives `T > (log₂ n − 1)/(⌈log₂ f⌉ + 1)`, without
the `+ 1`. Only the one-round case is refuted; for `T ≥ 2` the stated bound, and with it the claimed
`Ω((n/2)^{1+1/(k−1)})` messages for `k`-round algorithms, is unproved (the corrected bound gives `Ω(n^{1+1/k})`). Theorem 3.11 (`Ω(n log n)` messages for time-bounded algorithms) holds with explicit bound
`(n/2) log₂ n`, once the ID universe includes the `n log₂ n` IDs that Corollary 3.7 removes. Definition 3.5
must be read existentially; read literally, Lemma 3.6 and Corollary 3.7 are false. The algorithms of Theorems 3.10 and 3.15 are correct, with explicit constants.

## Mistakes in the paper

- **Theorem 3.8 is off by one round (false statement).** The paper claims: at most `n·f(n)` messages imply
  `T(n) > (log₂ n − 1)/(log₂ f(n) + 1) + 1`. Take `f(n) = n` and the algorithm in which every node sends its ID to
  everybody in round 1 and the maximum ID wins. It runs in `T = 1` round and sends `n(n − 1) ≤ n·f(n)` messages,
  for every ID universe. The claimed bound is `(log₂ n − 1)/(log₂ n + 1) + 1 > 1` for every power of two `n ≥ 2`.
  The cause is an index slip. The communication graph `G_r` only contains messages of rounds `< r`, but the proof
  applies Lemma 3.9 with `r = T`, so the messages of the last round are never accounted for. The induction step of
  Lemma 3.9 also builds `G_{r+1}` from the messages "sent during round `r+1`". Running the induction one round
  further gives the corrected bound `T > (log₂ n − 1)/(⌈log₂ f⌉ + 1)`, in fact `log₂ n ≤ (⌈log₂ f⌉ + 1)·T`.
  The "consequently" clause (`k`-round algorithms need `Ω((n/2)^{1+1/(k−1)})` messages) rests on the false
  bound. The corrected bound gives `Ω(n^{1+1/k})` (e.g. `Ω(n^{3/2})` instead of `Ω(n²)` for 2 rounds). That
  still improves polynomially on Afek–Gafni, but no longer matches the `O(n^{3/2})` 3-round algorithm of
  Theorem 3.10. Whether the stronger exponent holds is open. (`theorem_3_8_as_stated_false`,
  `theorem_3_8_corrected`, `rounds_messages_tradeoff`)
- **Ceiling (proof gap).** Theorem 3.8 is stated with `log₂ f(n)`, but the proof uses blocks of size
  `2^{(⌈log₂ f⌉+1)(r−1)}`. Its last inequality, `2^{σ_T} ≤ 2^{(log₂ f + 1)(T − 1)}`, goes the wrong way when `f`
  is not a power of two. We prove the version with `⌈log₂ f⌉`. (`theorem_3_8_corrected`)
- **Definition 3.5 is vacuous as written (defective definition).** "`X` forms terminating components if, for
  some `r`, in **every** restricted prefix `E ∈ Exec_r(X)` all nodes of `X` have terminated." This holds trivially
  when `Exec_r(X)` is empty, i.e. when some node of `X` must send on more than `|X| − 1` ports. For the broadcast
  algorithm every set of fewer than `n` IDs is then "terminating". Lemma 3.6 (at most `n/2^ℓ` disjoint
  terminating `2^ℓ`-sets) fails already for `n = 2` with three singletons, and so does Corollary 3.7. The proof of
  Lemma 3.6 actually uses the existential reading: *some* isolated execution of `X` exists. With that reading both
  results hold and suffice for Theorems 3.8 and 3.11. (`lemma_3_6_literal_false`, `not_disjoint_isolable`,
  `exists_universe_no_isolable_pow`)
- **Theorem 3.11: missing IDs (proof gap, minor).** Lemma 3.14 needs `n T'^{log₂ n − 1} + n log₂ n` IDs for the
  single-send algorithm, whose time is `T' = nT` (Lemma 3.12). Theorems 3.11 and 3.13 drop the `n log₂ n`. We prove
  Theorem 3.11 with `n log₂ n + n^{log₂ n} T^{log₂ n − 1}` IDs. (`theorem_3_11`)
- **Lemma 3.14 (proof gaps, statement true).**
  - Merging step: the ports opened by `C` are wired into `C'` by an arbitrary one-to-one map `g`, and those opened
    by `C'` into `C` by an independent `h`. A node can then receive two new links, which leaves capacity
    `2^i − 2`, not the claimed `|D|/2 − 1`. Wiring along one perfect matching `C ↔ C'` fixes this.
  - Counting: "`U_i` contains many pairwise disjoint sets" is not preserved by `|U_i'| ≥ |U_i|/T`. The
    pigeonhole must be applied to a disjoint subfamily.
  - Quantifiers: "every execution prefix in `Exec_{r_i}(I)`" is stronger than what the construction provides.
    One adversarial execution per set suffices.
  - Absorbing phase: how the first `|C|/2 − 1` new ports are kept inside `C` is left implicit. We track capacity
    per node. (`merge`, `level_step`, `absorb`)
- **Imprecisions in the algorithms (Theorems 3.10, 3.15; the results hold).**
  - Theorem 3.10: "there remains only a single survivor at the end of the `(k−1)`-th iteration" is not what the
    analysis shows. Up to `n^{1/(k−1)}` survivors can remain, and the final all-to-all round selects the maximum;
    its cost is within the claimed bound. The referee counts `⌈n^{i/(k−1)}⌉` can exceed `n − 1` for small `n`,
    so the algorithm caps them.
  - Algorithm 1 (Theorem 3.15) must stop nodes after they select a leader; otherwise later ID blocks keep
    broadcasting and the message bound fails. For `n = 1` the rule "select when receiving messages" never fires.
    The assumption `d ≤ n` is not needed.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

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
