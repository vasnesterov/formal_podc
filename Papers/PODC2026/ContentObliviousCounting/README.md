# Efficient Counting and Simulation in Content-Oblivious Rings — PODC 2026

Jérémie Chalopin, Yi-Jun Chang, Giuseppe Antonio Di Luna, Haoran Zhou. *Efficient Counting and
Simulation in Content-Oblivious Rings.* PODC 2026. DOI
[10.1145/3796701.3815917](https://doi.org/10.1145/3796701.3815917). Formalized version: arXiv
[2603.28260](https://arxiv.org/abs/2603.28260) v1 (full version; numbering follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Lemma 16 / Theorem 17 (bit sending has the composable ending
property) is false when the leader is a relay, a case the paper explicitly covers: two rounds run
back to back produce swapped outputs; the distance output of the §5 counting algorithm is also off
by one. The headline results hold: Theorems 1, 4, 5, 13, 14, 22 (with an active leader), Corollary
2, and the lower bound Theorem 3 (even per execution).

## Mistakes in the paper

* **The distance formula of the counting algorithm is off by one (false statement, §5 p. 9).**
  For every process probed in a completed phase (`myPhase < i`, including the last leader) the
  formula `myPhase(myPhase+1)/2 − k − 1` gives its clockwise distance minus one; it is undefined for
  the original leader (whose `myPhase` is never set). Already for `n = 2` the non-leader computes
  0, the leader's own distance. The correct value is `myPhase(myPhase+1)/2 − k` (and 0 for the
  leader); with it the algorithm computes `n` and all distances (Theorem 4).
  (`AnonCounting.paperResult_off_by_one`, `paperResult_wrong`, `paperResult_two`,
  `anonCount_final`)
* **Lemma 16 / Theorem 17: bit sending with a relay leader is not composable (false statement).**
  Lemma 16 explicitly covers a relay leader (Algorithm 8's lines 2–3 and 6 exist only for it) and
  Theorem 17 claims the composable ending property for it. But after forwarding the termination
  wave, the relay leader still reads *any* port, so it can consume a pulse that its
  already-returned clockwise neighbour sends in the next procedure. On 3 processes (relay leader
  `0`, active `1`, `2`) running two CCW rounds back to back — `1` sends `⊥` then `0`, `2` sends `⊥`
  twice — an execution of 16 deliveries ends in a final, quiescent configuration in which `2` has
  obtained `[0, ⊥]` instead of `[⊥, 0]`: the round-2 bit is attributed to round 1. Each single
  round is correct. Theorems 14 and 22 hold with an active leader (Theorem 14 assumes it;
  Theorem 22 as stated does not, and its proof does not cover a relay leader; neither does §9.2's
  use of relays, which may contain the leader). (`BitSending.relay_leader_composition_wrong`,
  `BitSending.not_composable_relay_leader`)
* **Theorem 1's λ-preprocessing does not work as written (pseudo-code error, easy fix).** With the
  input "ID length ≤ i" and "stop at the first false", the loop stops at `i = 1` (unless some ID has
  one bit) and "the largest index with outcome true" does not exist; the input must be
  "ID length ≥ i". Fixed in the formalization. Also, "self-decomposable for *disjoint* multisets"
  literally excludes counting (`{1} ⊎ {1}`); disjoint sets of processes are meant.
* **Algorithm 10 loops over the process's own input length (pseudo-code error, easy fix).**
  `while phase < len(bits)` lets processes with longer inputs call ComputeOR more often than the
  others, so the calls no longer match; the loop bound must be the common minimum length `B`
  (as the text suggests). Fixed in the formalization (Theorem 5).
* **Theorem 3's proof (minor proof gap, statement true).** The splicing in Lemma 28 ("replay O
  verbatim") cannot be literal — events of the removed part must be dropped and the kept interval's
  events rescheduled; we use a precise crossing-sequence merge. We prove more than stated:
  `n⌊log₂ n⌋ ≤ 14M + 4n` for *every* execution with `M` pulses in which the leader has counted.
  (`Counting.count_lower_bound`, `Counting.theorem3`, `Cslib.ContentOblivious.splice`)
* **Minor.** Lemmas 11–12 say the last phase is `⌈√n⌉`; there are about `√(2n)` phases (`n = 40`
  has 9). Lemma 10's premise has `p₀` uncounted and calls the per-phase invariant "immediate".
  Lemma 16 (relay segments behave like a link) is asserted without proof. Theorem 4 writes
  `d ∈ [0, n]`. Algorithm 5's comments say `phase > len` for `≥`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Content-oblivious oriented rings on `ZMod n`, every `n ≥ 1` (`n = 1` self-loop, `n = 2` double
  link) from `Cslib/Computability/Distributed/ContentOblivious/Model.lean`. Pulses carry nothing; a channel is a counter
  (equivalent to the paper's FIFO assumption). Asynchronous: at each step the adversary delivers
  any pulse in transit to a process willing to read that port (blocking receives on a given port
  or on any port). No failures; deterministic processes; all start at time 0.
* Exactly one leader. Inputs (leader flag, IDs, bits, messages, values) are node inputs of a
  `Prog I`. Anonymous where the paper is (Theorems 4, 5); distinct IDs for Theorems 1, 3, Cor. 2.
* "Quiescently terminating" = a bound on the pulses of every execution (so every execution is
  finite) and, in every *final* configuration (no step possible), all processes have returned and
  nothing is in transit. Pulse bounds hold for every reachable configuration.
* Composition (Theorem 9, Definition 8) is formalized semantically: `Proc.Composable` = bounded +
  quiescent termination + `clean` (a process that has not returned and waits on a link whose other
  end has returned has a pulse of the current procedure in transit). A general theorem runs any
  sequence of such procedures chosen by the processes' local states (loops included) and adds
  their pulse counts (`Cslib/Computability/Distributed/ContentOblivious/Staged.lean`); all composite algorithms of the paper
  (Algorithms 5, 6, 10, the simulator and Theorem 1's algorithm) are built this way.

**Main results in Lean.** (namespace `Cslib.ContentOblivious`; files in this folder unless noted)

| Paper | Lean | File |
|---|---|---|
| Theorem 9 (composition), generalized to staged programs | `Schedule.final`, `.totalSent_le`, `.composable` | `Cslib/Computability/Distributed/ContentOblivious/Staged.lean` |
| Theorem 21, Lemmas 18–20 (ComputeOR, exactly `3n` pulses) | `ComputeOR.composable`, `.returns`, `.totalSent_final`, `lemma18`–`lemma20` | `ComputeOR.lean` |
| Theorem 17, Lemmas 15–16 (bit sending, `≤ 6n`), CW mirror | `BitSending.returns`, `.composable`, `.totalSent_le`, `cw_*` | `BitSending.lean`, `Cslib/Computability/Distributed/ContentOblivious/Mirror.lean` |
| Lemma 16 / Thm 17 for a relay leader: **false** | `BitSending.relay_leader_composition_wrong`, `BitSending.not_composable_relay_leader` | `RelayLeaderComposition.lean`, `BitSending.lean` |
| Theorem 22 (MsgExchange, `15nL + 3n`) | `Concrete.theorem_22` | `MsgExchange.lean` |
| Theorem 14 (round-by-round simulation, `15nb + 3n` per round) | `Concrete.theorem_14` | `MsgExchange.lean` |
| Theorem 4, Theorem 13, Lemmas 10–12 (anonymous counting) | `AnonCounting.anonCount_final`, `anonCount_composable`, `totalPulses_le_sqrt` | `AnonCountingMain/Bounds/Compose.lean` |
| Distance formula: **off by one** | `AnonCounting.paperResult_off_by_one`, `paperResult_two` | `AnonCountingBounds.lean` |
| Lemma 26 (Cole–Vishkin MIS on a virtual ring) | `Aggregation.lemma26` | `AggregationMIS.lean` |
| Theorem 1 (aggregation) | `Aggregation.theorem1_concrete` | `AggregationConcrete.lean` |
| Corollary 2 (`O(n log² n)` counting) | `Aggregation.corollary2_concrete` | `AggregationConcrete.lean` |
| Theorem 5, Algorithm 10 (minimum finding, `6n·|xmin|`) | `Concrete.theorem_5` | `MsgExchange.lean`, `MinFindingGeneric.lean` |
| Observation 27, Lemma 28 (splicing) | `Counting.observation27`, `Counting.lemma28` | `LowerBoundSplice.lean`, `Cslib/Computability/Distributed/ContentOblivious/Splice.lean` |
| Theorem 3 (lower bound), per execution and in the paper's form | `Counting.count_lower_bound`, `Counting.theorem3` | `LowerBound.lean` |

**Not formalized.** Theorem 6 (multiset computation), Theorem 7 and §7 (2-edge-connected
networks: relies on results of Censor-Hillel et al. and Alon–Tarsi), Theorem 22 with a relay leader.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. All composite results are instantiated with the formalized Algorithms 7–9 (no
hypotheses left). Non-vacuity: the lower bound's hypothesis is met by the counting algorithm of
Theorem 4 (`Counting.countingCorrect_anonCount`, `LowerBoundNonVacuity.lean`), whose
`O(n^1.5)` bound sits above the `Ω(n log n)` bound. A bounded model check of the paper's
pseudo-code (`modelcheck/`) found no errors beyond those listed above. Generic infrastructure
(upstreamed to CSLib) is in `Cslib/Computability/Distributed/ContentOblivious/`: `Prog`, `Compose`, `Staged`, `Hom`, `Mirror`,
`Splice`, `VirtualRing`.
