# Blunting an Adversary with Linearizable Implementations — PODC 2022

Hagit Attiya, Constantin Enea, Jennifer L. Welch. *Blunting an Adversary Against Randomized Concurrent Programs
with Linearizable Implementations.* PODC 2022. DOI [10.1145/3519270.3538446](https://doi.org/10.1145/3519270.3538446).
Formalized version: arXiv 2106.15554v2 (full version with appendix).

**Verdict: ⚠️ Weakened.** Lemmas 4.3 and 4.4, on which the proof of the main theorem rests, are false
(Lean counterexamples), and the simulating adversary used in their proofs is not a valid adversary.
Theorem 4.2 holds as stated for programs with one random step, and a weaker bound, which still gives
convergence to atomic objects, holds for any number of random steps; for `r ≥ 2` the stated bound
remains unestablished (neither proved nor refuted here). Only shared-memory objects are covered: the
application to ABD, snapshots and the other implementations of Section 5 was not checked.

## Mistakes in the paper

### ⚠️ Lemmas 4.3 and 4.4, and Theorem 4.2 (main theorem) for `r ≥ 2`
Lemmas 4.3 and 4.4 are false because conditioning on `X` biases the program's own coins, and Theorem 4.2 is unestablished for programs with `r ≥ 2` random steps, since its proof is the decomposition (1)–(2) over `X`, which needs the two false lemmas.

**Impact.** The stated bound holds for `r = 1` (the only case used in the paper's example,
Appendix A.3.1) and in a weaker form for every `r`; for `r ≥ 2` it is neither proved nor refuted here
(`theorem_4_2_r1`, `theorem_4_2_weak`). The instance below does not refute Theorem 4.2 itself.

**Details.** Lemma 4.3 claims `Prob[(P(O^k)||A → B) | X] ≤ Prob[P(O^a) → B]` for every adversary `A`. In a
two-process program with one register, one object read with a one-step preamble and two coins, an adaptive
adversary with `k = 2` gets `Pr[B | X] = 2/3 > 1/2` (`Counterexample.lemma_4_3_false`). In the same instance,
the adversary that overlaps only when `c1 = 1` gets `Pr[B | ¬X] = 1`, while `Prob[P(O) → B] ≤ 1/2`, which
refutes Lemma 4.4 (`Counterexample.lemma_4_4_false`).

`X` = "every object random step picks a randomization-free preamble iteration". Conditioning on
`X` biases the program's own coins: the adversary can decide, after seeing the first coin, whether the
preamble iteration that might be chosen later overlaps the second coin. Instance: processes `p, q`; a
register `R` and an object `S` whose read has a one-step preamble (the object is strongly linearizable, so
all hypotheses of Theorem 4.2 hold, with `r = 2`); `p: c1 := coin; R.write(c1); c2 := coin`,
`q: S.read(); y := R.read()`, `B = {y = 1}`. With atomic objects (and with the original object) `Pr[B] ≤ 1/2`
for every adversary. With `k = 2`, the adversary that lets `q` start `S.read` before `p`'s write and `c2` only
when `c1 = 0` gets `Pr[B | X] = 2/3`.

**Repair.** For every `r` we prove `Prob[O^k] ≤ Prob[O^a] + (1 − q)` and `Prob[O^k] ≤ Prob[O]` with
`q = (max{0,k−r}/k)^{n−1}`. The stated bound `Prob[O^a] + (1−q)(Prob[O] − Prob[O^a])` is stronger whenever
`Prob[O] < 1`. A repair of the stated bound along the lines of the paper fails when the adversary makes the
choice of which iterations get spoiled at a later coin depend on earlier coins.

### 🛠️ Proofs of Lemmas 4.3 and 4.4 (the adversary `A_O`)
The simulating adversary `A_O` built in these proofs is not a valid adversary, because its schedule depends on future coins.

**Impact.** The simulation of `P(O^k)` by `P(O)` with unused iterations removed is saved by a new argument,
which the bounds above use (`Removal.opt_le_avg`, `prob_iter_le_prob_impl`, `optBX_le_prob_atom`).

**Details.** The adversary `A_O` chooses each object random value as the "best" one *after* later program
coins, and `remRedundant` moves preamble steps relative to earlier coins, which violates the paper's own
definition of an adversary.

**Repair.** The object random choices are independent of everything the adversary sees before they are
made, so they can be sampled in advance; for each advance choice the removal of unused iterations is a
causal adversary against `P(O)` (`Removal.opt_le_avg`).

### ✏️ Slips
- Theorem 3.1 speaks of tail strong linearizability of a set of *histories*, which is not defined (the
  notion needs executions and control points).

## Proof gaps (statements true)

### 🛠️ Lemma 4.5 (probability of `X`)
The proof treats the events `X_i` as independent with fixed probabilities, although the set of spoiled iterations depends adaptively on earlier choices.

**Impact.** Statement true; proved by a potential argument (`lemma_4_5`, `Clean.optNX_le`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, no failures. Objects are deterministic implementations from atomic base objects
  (CSLib `Impl`), all operations allowed; a finite set of objects is one combined object. Message-passing
  implementations (ABD) are not covered.
- Programs: one deterministic client per process with local steps, `random(V)` (uniform over `m+1` values) and
  object calls. Outcomes are final client states (at least as general as the paper's return-value outcomes).
- Strong adversary: chooses the next process with full knowledge of the configuration (hence of all past
  random values). `Prob[P(O) → B]` (`prob`) is the optimal value of the resulting finite-horizon game
  (`MDP.opt`, supremum over horizons; non-terminating runs do not count), i.e. the supremum over all strong
  adversaries. Conditional probabilities in the counterexamples use the value of a fixed adversary.
- Preamble mapping = predicate "the local state is still inside the preamble" with well-formedness
  (`PreambleWF`); effect-free = preamble steps apply read-only primitives (`EffectFree`); tail strong
  linearizability (`TailStronglyLinearizable`) = linearizable + prefix-preserving linearization function on
  executions in which every pending invocation has passed its preamble.
- `O^k` (`iterSem`, Algorithm 2): `k` preamble iterations from the post-invocation local state, then one
  uniform choice; ghost fields record which iterations overlapped a program random step (event `X`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.2, `r = 1` (as stated) | `theorem_4_2_r1` | `Main.lean` |
| Theorem 4.2, any `r` (weaker bound) | `theorem_4_2_weak`, `theorem_4_2_corrected` | `Theorem42.lean` |
| Theorem 4.1 (consequence `Prob[O^k] ≤ Prob[O]`) | `prob_iter_le_prob_impl` | `Main.lean` |
| Lemma 4.3 — false | `Counterexample.lemma_4_3_false` | `Counterexample.lean` |
| Lemma 4.3, corrected (`Pr[B ∧ X] ≤ Prob[O^a]`) | `optBX_le_prob_atom` | `Main.lean` |
| Lemma 4.4 — false | `Counterexample.lemma_4_4_false` | `Counterexample.lean` |
| Lemma 4.5 | `lemma_4_5` (proof `Clean.optNX_le`) | `Theorem42.lean`, `Clean.lean` |
| Lemma 4.3, property (4) (TSL ⇒ simulation by atomic objects) | `optSafe_le_prob_atom` | `TSLSim.lean` |
| Theorem 2.3, direction `Prob[O] ≤ Prob[O^a]` | `prob_impl_le_atom_of_stronglyLinearizable` | `Main.lean` |
| removal of unused iterations (repaired `remRedundant`) | `Removal.opt_le_avg` | `Removal.lean` |

**Not formalized.** Propositions 2.1–2.2, Theorem 3.1, the converse direction of Theorem 2.3, the
history-equivalence part of Theorem 4.1, Section 5 (ABD, snapshot, multi-writer and multi-reader registers are
tail strongly linearizable), Appendix A. Whether the bound of Theorem 4.2 is true for `r ≥ 2` remains open here:
it is neither proved nor refuted.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The counterexample instance satisfies every hypothesis of the paper's setting (tail strong linearizability —
even strong linearizability, via CSLib `OneAccess` —, effect-free and well-formed preambles, at most two random
steps). Shared-memory model, histories and linearizations come from CSLib
(`Cslib.Computability.Distributed.SharedMemory`).

CSLib candidates (marked `-- CSLib candidate`): the strong-adversary game layer `MDP.lean` (values,
supersolution bound), the composition of programs with implemented objects (`Model.lean`), and the
Golab–Higham–Woelfel-style simulation of (tail) strongly linearizable implementations by atomic objects
(`TSLSim.lean`).
