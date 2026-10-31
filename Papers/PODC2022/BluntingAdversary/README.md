# Blunting an Adversary with Linearizable Implementations — PODC 2022

Hagit Attiya, Constantin Enea, Jennifer L. Welch. *Blunting an Adversary Against Randomized Concurrent Programs
with Linearizable Implementations.* PODC 2022. DOI [10.1145/3519270.3538446](https://doi.org/10.1145/3519270.3538446).
Formalized version: arXiv 2106.15554v2 (full version with appendix).

**Verdict: ❌ False claim.** Lemmas 4.3 and 4.4, on which the proof of the main theorem rests, are false
(Lean counterexamples), and the simulating adversary used in their proofs is not a valid adversary. The main
Theorem 4.2 holds as stated for programs with one random step, and a weaker bound holds for any number of
random steps; for `r ≥ 2` the stated bound remains unestablished (neither proved nor refuted here).

## Mistakes in the paper

- **Lemma 4.3 is false.** It claims `Prob[(P(O^k)||A → B) | X] ≤ Prob[P(O^a) → B]` for every adversary `A`,
  where `X` = "every object random step picks a randomization-free preamble iteration". Conditioning on `X`
  biases the program's own coins: the adversary can decide, after seeing the first coin, whether the
  preamble iteration that might be chosen later overlaps the second coin. Instance: processes `p, q`; a register
  `R` and an object `S` whose read has a one-step preamble (the object is strongly linearizable, so all
  hypotheses of Theorem 4.2 hold, with `r = 2`); `p: c1 := coin; R.write(c1); c2 := coin`, `q: S.read();
  y := R.read()`, `B = {y = 1}`. With atomic objects (and with the original object) `Pr[B] ≤ 1/2` for every adversary. With `k = 2`, the
  adversary that lets `q` start `S.read` before `p`'s write and `c2` only when `c1 = 0` gets
  `Pr[B | X] = 2/3`. (`Counterexample.lemma_4_3_false`)
- **Lemma 4.4 is false.** Same instance; overlapping only when `c1 = 1` gives `Pr[B | ¬X] = 1`, while
  `Prob[P(O) → B] ≤ 1/2`. (`Counterexample.lemma_4_4_false`)
- **The adversary `A_O` built in these proofs is not an adversary.** It chooses each object random value as
  the "best" one *after* later program coins, and `remRedundant` moves preamble steps relative to earlier
  coins, so its schedule depends on future coins (violating the paper's own definition of an adversary).
  The repair: the object random choices are independent of everything the adversary sees before they are
  made, so they can be sampled in advance; for each advance choice the removal of unused iterations is a
  causal adversary against `P(O)`. (`Removal.opt_le_avg`)
- **Theorem 4.2 is unestablished for `r ≥ 2`.** Its proof is the decomposition (1)–(2) over `X`, which needs
  the two false lemmas. We prove the stated bound for `r = 1` (the only case used in the paper's example,
  Appendix A.3.1) and, for every `r`, `Prob[O^k] ≤ Prob[O^a] + (1 − q)` and `Prob[O^k] ≤ Prob[O]` with
  `q = (max{0,k−r}/k)^{n−1}`. The stated bound `Prob[O^a] + (1−q)(Prob[O] − Prob[O^a])` is stronger whenever
  `Prob[O] < 1`; a repair along the lines of the paper fails when the adversary makes the choice of which
  iterations get spoiled at a later coin depend on earlier coins. (`theorem_4_2_r1`, `theorem_4_2_weak`)
- Minor: the proof of Lemma 4.5 treats the events `X_i` as independent with fixed probabilities although the
  set of spoiled iterations depends adaptively on earlier choices (the bound is nevertheless true, proved by
  a potential argument); Theorem 3.1 speaks of tail strong linearizability of a set of *histories*, which is
  not defined (the notion needs executions and control points).

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

**Not formalized.** Propositions 2.1–2.2, Theorem 3.1, the history-equivalence part of Theorem 4.1,
Section 5 (ABD, snapshot, multi-writer and multi-reader registers are tail strongly linearizable), Appendix A.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The counterexample instance satisfies every hypothesis of the paper's setting (tail strong linearizability —
even strong linearizability, via CSLib `OneAccess` —, effect-free and well-formed preambles, at most two random
steps). Shared-memory model, histories and linearizations come from CSLib
(`Cslib.Computability.Distributed.SharedMemory`).

CSLib candidates (marked `-- CSLib candidate`): the strong-adversary game layer `MDP.lean` (values,
supersolution bound), the composition of programs with implemented objects (`Model.lean`), and the
Golab–Higham–Woelfel-style simulation of (tail) strongly linearizable implementations by atomic objects
(`TSLSim.lean`).
