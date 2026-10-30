# Energy-Efficient Distributed Agreement — PODC 2025

Hugo Mirault, Peter Robinson. *Brief Announcement: Towards Energy-Efficient Distributed Agreement.* PODC 2025.
DOI [10.1145/3732772.3733554](https://doi.org/10.1145/3732772.3733554). Formalized version: the brief announcement,
with the algorithms and proofs of its full version arXiv [2506.12282](https://arxiv.org/abs/2506.12282) **v1**
(cited as [12] for the omitted proofs; Algorithm 1/Lemmas 1–4 of the BA = Algorithm 2/Lemmas 2–5 there, Theorem 2 of
the BA = Theorem 6 there). arXiv v2 is a different, later paper (OPODIS 2025, with Meir and Peleg) with a redesigned
binary algorithm; it is not formalized here.

**Verdict: ❌ False claim.** The multi-value result (Theorem 1) holds: Algorithm 1 solves crash consensus in `f + 1`
rounds with `2 + 2⌈f(f+1)/n⌉` awake rounds per player and `O(f³ + nf)` messages. Its proof needs one repair, and
Lemma 2 is false as literally stated. The binary-consensus result (Theorem 2) is not established. The algorithm
behind it, sketched in the BA and given as Algorithm 3 in the full version, **violates agreement**, e.g. for
`n = 5`, `f = 3`. The claim itself is existential, so it is not refuted: ❌ rather than 🚨 (R5).

## Mistakes in the paper

* **Theorem 2: the binary consensus algorithm violates agreement.** Take `n = 5`, `f = 3`. Committees
  (`JoinCommittees(3, 3)`): `C₁ = {p₁,p₂,p₃}`, `C₂ = {p₄,p₀,p₁}`, `C₃ = {p₂,p₃,p₄}`, and `T = ⌈4/√5⌉ = 2`. Only
  `p₂` has input 1. The run goes as follows.
  - Round 1: `p₂` crashes, and its message reaches only `p₃ ∈ C₁`.
  - Round 2: `p₃` (now active) crashes, reaching only `p₄ ∈ C₂`.
  - Round 3: `p₄` relays `1` to `C₃ = {p₂,p₃,p₄}`. All other members of `C₃` have already crashed, so the adversary
    does not need to crash anyone in this round.
  - Round 4 = `f + 1`: `p₄` broadcasts and crashes, reaching only `p₀`.

  With only 3 crashes, the non-faulty `p₀` decides 1 and `p₁` decides 0. The gap is the paper's counting
  argument: a relay round does not always produce a new holder of `1` or force a new crash. A message can go to a
  committee whose members have all crashed already, or to the relay itself. The same works for `n = 7, f = 4`
  (three non-faulty players) and for the perfect square `n = 9, f = 7`. For `n = s²`, `f = n − 2`, a relay chain whose receivers are taken from `C₁ = C_{1+s} = …`
  whenever possible eventually makes such a round free. A simulation (`scripts/family.py`) confirms this for all
  `3 ≤ s ≤ 12`. The BA's sketch (committees
  "analogous" to Algorithm 1, unspecified) is affected just as much. A model check shows that for `n = 5`,
  `f = 3`, **every** choice of 3 committees of size 3 admits a disagreeing execution. In the full version, Lemma 11
  (used for Lemma 12, agreement) is false: in the run above `|P₄| = 3 ≤ f`, yet agreement on 0 fails. The full version's
  claim that a player in `C_i` is in none of `C_{i+1}, …, C_{i+⌈√n⌉+1}` is also wrong. `JoinCommittees` does not
  guarantee it, and no assignment can once `f > ⌈√n⌉`, or `f = ⌈√n⌉` with `n` not a perfect square, as in the `n = 5`, `f = 3`
  run (it would need `min(f, ⌈√n⌉+2)` pairwise-disjoint committees of size `⌈√n⌉`, i.e. more than `n` players). The
  authors' later OPODIS 2025 version describes this exact attack ("crash players, one at each round, such that
  eventually … all the members of a committee have already crashed") and redesigns the algorithm. That redesign is
  not checked here. (`algorithm3_violates_agreement`, `algorithm3_violates_agreement_7_4`,
  `algorithm3_violates_agreement_9_7`)
* **Lemma 2 is false as stated.** It assumes only that `p` is *alive in round `i`*, which the paper defines as not
  crashed in rounds `1, …, i − 1`. Then `p` may crash in round `i` itself and lose its message. Example: `n = 2`,
  `f = 1`, inputs `5, 0`. `p₀` sends `5` to `C₁` in round 1 and crashes, reaching nobody; `p₁` decides `δ = 0 < 5`.
  The proof says that `p` "successfully sends its message to all destinations", so the intended hypothesis is "does
  not crash in round `i`". We prove that version: every decision is `≥ v`. (`lemma_2_as_stated_false`,
  corrected `lemma_2`)
* **Lemma 4 (agreement): proof gaps, statement true.** The proof treats the first clean round `t` only for `t = 1`
  and `1 < t < f + 1`; the case `t = f + 1` is missing. In the main case it concludes "since `p` does not crash" for
  an arbitrary alive holder `p` of `δ`, which may crash later. The repair uses two facts. After a clean round
  `t ≤ f`, **all** alive members of `C_t` hold the same value, because every one of them received every alive
  member of `C_{t−1}`, whose maximum dominates their own earlier values by Lemma 3 (`mv_clean_le`). And `C_t` has a
  non-faulty member, which carries this value to the end. If `t = f + 1`, every decider receives the values of all
  alive members of `C_f`, and Lemma 3 bounds its own value. (`lemma_4`)
* Minor: Lemma 3's hypothesis `m ≥ δ` is unnecessary (proved without it, `lemma_3`). Algorithm 1 needs `f ≥ 1`,
  since it refers to `C_f`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/SleepingCrash/Model.lean`, staged, CSLib candidate).
- Synchronous rounds `1, 2, …` on a complete network of `n` players with unique IDs, in the sleeping model. In each
  round a player is awake or asleep, as a function of the round and of its state at the start of the round (an
  "alarm" set when it was last awake). Asleep players send nothing, receive nothing (messages to them are lost) and
  do not change state.
- Crash faults: an omniscient adversary fixes the inputs and, for at most `f` players, a crash round `c ≥ 1` and the
  subset of recipients that still get the player's round-`c` messages. Afterwards the player sends nothing.
  Deterministic algorithms, no randomness.
- Deciders are the players that complete round `f + 1`. Agreement and validity are proved for all of them. Energy is
  the number of rounds in `1..f+1` in which a player is awake before crashing (`awakeCount`). Messages are counted as
  sent, including those lost (`msgCount`).
- Multi-value inputs come from any linearly ordered type (the paper uses integers).

**Main results in Lean** (namespace `Podc.EnergyEfficientAgreement`).

| Paper | Lean | File |
|---|---|---|
| Algorithm 1 (BA) / 2 (full) | `multiValue f C` | `MultiValue.lean` |
| `JoinCommittees(a, b)`: sizes, `≤ ⌈ab/n⌉` memberships | `joinCommittees`, `card_joinCommittees`, `card_filter_mem_joinCommittees_le` | `Committees.lean` |
| Lemma 1 (validity; termination in `f + 1` rounds by construction) | `mv_validity` | `MultiValue.lean` |
| Lemma 2 as stated — **false** | `lemma_2_as_stated_false` | `MultiValue.lean` |
| Lemma 2 (corrected: `p` does not crash in round `i`) | `lemma_2` | `MultiValue.lean` |
| Lemma 3 (without `m ≥ δ`) | `lemma_3` | `MultiValue.lean` |
| Lemma 4 (agreement, any committees of size `> f`) | `lemma_4` | `MultiValue.lean` |
| Energy / message bounds of Theorem 1 | `mv_awakeCount_le`, `mv_msgCount_le` | `MultiValue.lean` |
| **Theorem 1** (agreement, validity, energy `2 + 2⌈f(f+1)/n⌉`, messages `(f+1)³ + 2n(f+1)`) | `theorem_1` | `MultiValue.lean` |
| Theorem 2 / Algorithm 3 (full) | `binary`, `algorithm3` | `Binary.lean` |
| Theorem 2 — **agreement fails** (`n = 5, f = 3`; `7, 4`; `9, 7`) | `algorithm3_violates_agreement`, `algorithm3_violates_agreement_7_4`, `algorithm3_violates_agreement_9_7` | `Binary.lean` |

**Not formalized.** Message sizes in bits (each message is one value or one bit). The `O(n²)` message and
`O(⌈f/√n⌉)` energy bounds of Theorem 2, which are moot since the algorithm is incorrect. The repaired binary
algorithm of the OPODIS version. The family `n = s², f = n − 2` and the all-committee-assignments check for `n = 5` are
Python checks only (`scripts/family.py`, `scripts/allcomm.py`; exhaustive adversary search for small `n` in
`scripts/binmc.py`, restricted search in `scripts/chain.py`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Counterexample executions are evaluated by `decide` on the computable model, with the real ceilings `⌈√n⌉₊`,
`⌈(f+1)/√n⌉₊` evaluated first. Sanity checks: a crash-free run of Algorithm 3 in which everybody decides 1, and
admissibility of crash-free adversaries for `theorem_1`. Uses `Nat.card_Ico_filter_modEq_le` from CSLib.
CSLib candidate: `Podc/Computability/Distributed/SleepingCrash/Model.lean`.
