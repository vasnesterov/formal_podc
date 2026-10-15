# On the Validity of Consensus — PODC 2023

Pierre Civit, Seth Gilbert, Rachid Guerraoui, Jovan Komatovic, Manuel Vidigueira. *On the Validity of Consensus.*
PODC 2023. DOI [10.1145/3583668.3594567](https://doi.org/10.1145/3583668.3594567). Formalized version: extended
version arXiv:2301.04920v3 (numbering follows it).

**Verdict: ✅ Correct.** The classification of solvable validity properties is proved: trivial ones for
`n ≤ 3t`, and those satisfying the similarity condition `C_S` for `n > 3t`. So is the `Ω(t²)` message lower bound.
The sufficiency direction is unconditional, because we also verified a vector-consensus protocol for every
`n > 3t`; this replaces the paper's black box. The only proof gap is in Lemma 3 for `n < 2t`, and it is easily
repaired.

## Mistakes in the paper

- **Lemma 3 (proof of Theorem 1) breaks down for `n < 2t` (proof gap; statement true).** The proof builds a
  configuration in `I_{n−t}` from *all* `t` processes outside `π(base)` plus `n − 2t` processes of `π(base)`. For
  `n < 2t` this is impossible: `t` processes do not fit into a configuration of size `n − t`, and `n − 2t < 0`.
  The smallest instance is `n = 3`, `t = 2`, which the paper allows (`0 < t < n ≤ 3t`). Repair: take
  `min(t, n − t)` processes outside `π(base)` and fill up from `π(base)`. This configuration is compatible with
  `base` in the whole range. (`trivial_of_solvesConsensus_auth`)
- **Theorem 2 is formally trivial.** "A finite procedure returning an always-admissible value" exists as soon as
  one always-admissible value exists, which Theorem 1 gives: return that constant. (`alwaysAdmissible_computable`)
- **Theorem 3's "Turing-computable Λ" needs computable algorithms.** The model allows arbitrary deterministic
  state machines. Solvability then only yields *some* function `Λ`, not a computable one. We prove both versions:
  any `Λ` for arbitrary algorithms, and a computable `Λ` (in Mathlib's sense) when the algorithm's transition
  functions are computable. (`similarityCondition_of_solvable`, `similarityCondition_computable`)
- **Implicit assumptions.**
  - The proposal set must be nonempty. Otherwise there are no executions and Theorem 1 fails vacuously.
  - Agreement must also cover `p = q`, i.e. a process decides at most once.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** A shared partially synchronous Byzantine model (`Cslib.Byzantine.PartialSync`).
- `n` processes; at most `t` are statically Byzantine with arbitrary behaviour. Algorithms are deterministic,
  links are authenticated point-to-point, and there is no randomness.
- Discrete time with an unknown GST and a known `δ`. Correct processes step at every tick from time 0, so they have
  drift-free clocks and are always awake. "Waking up late" is simulated by delaying a process's messages.
- Optional ideal signatures (unforgeable tokens, eavesdropping rushing adversary). All impossibility results are
  proved with signatures and specialized to the plain model.
- Message complexity counts messages from correct processes to *other* processes after GST.
- **Effect on the results.** The adversary is weaker than the paper's: it has no clock drift and no sleeping
  processes before GST. This makes the impossibilities (Theorems 1, 3, 4) stronger. The possibility side (vector
  consensus, Theorem 5, the full classification) is correspondingly weaker. Lifting it to the paper's model would
  need a view synchronizer, which is not formalized.
- Solvability quantifies over algorithms whose state and message types are in `Type`.

**Main results in Lean** (namespace `ValidityConsensus`).

| Paper | Lean | File |
|---|---|---|
| Lemmas 1–2 (canonical similarity, merging) | `canonical_similarity`, `eq_of_compatible` | `Triviality.lean` |
| **Theorem 1** (`n ≤ 3t`: solvable ⇒ trivial) | `trivial_of_solvable`, `trivial_of_solvableAuth` | `Triviality.lean` |
| Theorem 2 | `alwaysAdmissible_computable` | `SimilarityComputable.lean` |
| **Theorem 3** (`C_S` necessary) | `similarityCondition_of_solvable`, `similarityCondition_computable` | `Similarity.lean`, `SimilarityComputable.lean` |
| **Theorem 4** (`> ⌈t/2⌉²` messages) | `message_complexity_lower_bound`, `message_lower_bound` | `LowerBound.lean` |
| **Theorem 5** (Universal, given vector consensus) | `solvesConsensus_universal`, `solvable_of_similarityCondition` | `Universal.lean` |
| Vector consensus for `n > 3t` | `vectorConsensusSolvable` | `Optimal.lean` |
| **Classification** (Fig. 1), unconditional | `solvable_iff` | `Optimal.lean` |
| Non-vacuity: binary strong validity solvable at `n > 3t`, Thm. 4 applies | `strongValidity_solvable_optimal`, `optimal_message_lower_bound` | `Optimal.lean` |

`message_lower_bound` is slightly stronger than Theorem 4: some run with `gst = 0` has at least
`⌈t/2⌉(⌈t/2⌉ + 1)` messages within finite time.

**Not formalized.**
- The paper's own vector-consensus protocols (Quad, DBFT with reliable broadcast) and their `O(n²)` message
  complexity. Our verified protocol is a different PBFT-style protocol in a round layer, with much higher message
  complexity.
- Appendix C (external validity) and the randomized remark.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
model, the round layer and the vector-consensus protocol are in CSLib,
`Cslib/Computability/Distributed/Byzantine/PartialSync/` (protocol in `VC/`). The model is shared with the PODC 2021
*Fast Byzantine Consensus* formalization, which reuses Theorem 1.
