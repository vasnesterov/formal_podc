# Synchronous Approximate Agreement with Asynchronous Fallback — PODC 2022

Diana Ghinea, Chen-Da Liu-Zhang, Roger Wattenhofer. *Optimal Synchronous Approximate Agreement with
Asynchronous Fallback.* PODC 2022. DOI [10.1145/3519270.3538442](https://doi.org/10.1145/3519270.3538442).
Formalized version: the PODC proceedings version (no arXiv version exists). Numbering follows it. The full
version (IACR ePrint 2022/354, single version of 2022-03-18) has the same protocols and statements; it contains
the proof of Theorem 4.1 (Section 6.1).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The impossibility result (Theorem 5.1: no AA protocol when `2tₛ + tₐ ≥ n`) is
correct for `n ≥ 2`, even with signatures. The protocol side is broken. The Reliable Broadcast `Π_rBC` is
not consistent in a synchronous network when `tₛ ≥ n/3` (Theorem 4.1 is false). As a result, the main
protocol `Π_AA` is **not** a `tₛ`-secure AA protocol in the synchronous network (Theorem 3.1(1) is false).
For `n = 3`, `tₛ = 1`, `tₐ = 0`, one Byzantine party keeps the two honest parties at `0` and `1` forever.
The iteration analysis (Lemmas 3.2–3.7) is correct *if* the Overlap All-to-All Broadcast has the
guarantees of Definition 2.2. So the headline tight characterization is only half established by the paper.

## Mistakes in the paper

* **Theorem 4.1 is false: `Π_rBC` is not consistent in a synchronous network when `tₛ ≥ n/3`.**
  Lines 2–4 detect a Byzantine sender's equivocation only for proposals that arrive by time `Δ`. Their
  forwards then reach everybody by `2Δ`, as the paragraph before the pseudocode argues. The failing step is
  in the proof of Lemma 6.2 of the full version: "as `P` sent a vote for `v` at time `τ`, `P` has received
  and forwarded a valid propose message for `v` at time `τ − Δ`". By line 4, `P` forwards and votes at the
  same time when the proposal arrives at `2Δ`. But a
  Byzantine sender may deliver its proposals *late*. Take `n = 3`, `tₛ = 1`, `tₐ = 0`, honest `P₀`, `P₁`,
  and a Byzantine sender `C`. `C` sends `propose 0` to `P₀` and `propose 1` to `P₁`, both arriving at
  time `2Δ`. Each honest party has seen no conflicting proposal, so it forwards its proposal and votes
  for it at `2Δ`. The conflicting forwards arrive only at `3Δ`. `C` votes for both values. At `3Δ`,
  `P₀` holds the `n − tₛ = 2` votes `{P₀, C}` for `0` and outputs `0`, while `P₁` holds `{P₁, C}` for
  `1` and outputs `1`. Both parties output at `3Δ`, so `(tₛ,1)`-Synchronized Consistency fails. The
  run is synchronous (every honest message arrives after exactly `Δ`), has one corruption and forges
  no signature. The same idea works whenever `n ≤ 3tₛ`: split the honest parties into two groups of
  size `≥ n − 2tₛ` each. So the theorem fails for every `tₛ` in the paper's range `n/3 ≤ tₛ < n/2`;
  only `n = 3` is formalized. Severity: false statement. (`RBC.rbc_not_syncConsistent`,
  `RBC.rbc_attack`)
* **Theorem 3.1 (1) is false: `Π_AA` does not achieve agreement in a synchronous network.** The proofs
  of Lemma 4.3 ("`Π_rBC` guarantees that `P′` has received each value reported by `P`") and of Lemma 4.4
  (`tₛ`-Consistency of `Π_oBC`) rely on Theorem 4.1. So does Lemma 3.3 (`|V ∪ V′| ≤ n`). We ran the
  whole protocol in the setting above (`n = 3`, `tₛ = 1`, `tₐ = 0`, `ε = 1/2`, `δmax = 1`, hence
  `S = 1` iteration). Honest inputs are `0` and `1`. `C` performs the above attack in its own `Π_rBC`
  instance. It then reports to each honest party exactly that party's set `O`, so `C` becomes a
  witness of both. Both honest parties terminate `Π_oBC` just after `4Δ`, with `O₀ = {0, 1, 0}` and
  `O₁ = {0, 1, 1}`. Discarding one value at each end gives the outputs `0` and `1`. The range of
  honest values is not halved at all, and the attack can be repeated in every iteration. Validity
  and termination are not violated; agreement is. If `C` instead withholds its reports, neither
  honest party ever terminates `Π_oBC`. This contradicts Lemma 4.3 too; we checked it by running the
  encoding, not by a proof. Severity: false statement for the protocol as
  written. The characterization claimed in the abstract may still hold with a correct hybrid
  broadcast primitive, but the paper does not establish it. (`AA.theorem_3_1_sync_false`)
* **Theorem 5.1 needs `n ≥ 2`.** For `n = 1` (e.g. `tₛ = 0`, `tₐ = 1`, so `2tₛ + tₐ ≥ n`), "output
  your input" is a secure AA protocol. Severity: false only in a degenerate case.
  (`theorem_5_1_false_n_eq_one`)
* **Theorem 5.1, proof gaps (statement true for `n ≥ 2`).** The proof says "let `n = 2tₛ + tₐ`".
  This reduction is not always possible. For example, `n = 3`, `tₛ = 2`, `tₐ = 0` has no thresholds
  `t′ₛ ≤ tₛ`, `t′ₐ ≤ tₐ` with `2t′ₛ + t′ₐ = 3`. The fix is to use groups of size *at most* `tₛ`/`tₐ`.
  If `tₛ = 0`, the groups `S±ε` are empty and the argument gives nothing. The fix is to use groups of
  size `≤ max(tₛ, tₐ)`, with scenarios 1 and 2 read as asynchronous executions when needed (a
  synchronous execution is also an asynchronous one). (`exists_split`, `not_secure_sync_and_psync`)
* **Definition 2.2 is incomplete for the asynchronous analysis.** Lemma 3.4 uses that "at most `tₐ`
  values are sent by corrupted parties". This needs the value attributed to an *honest* sender to be
  its actual input, which Definition 2.2 does not require in the asynchronous case. It holds for the
  concrete `Π_oBC`, so this is a gap in the interface, not in the result. We add it as the hypothesis
  `AsyncOBC.authentic`. Severity: under-specified definition.
* **Definition 2.1 does not require termination**, while the impossibility proof uses it ("the honest
  parties output +ε"). We include termination in the definition. Severity: under-specified definition.
* **Typos.** In Lemma 3.6, "`0 ≤ tₐ, c ≤ tₛ`" should read `0 ≤ tₐ ≤ tₛ` (`c` is not defined there).
  In the proof of Lemma 3.6, "`i_v + m_V(u) − 1`" should be `i_u + …`. In Lemmas 3.3 and 3.5,
  "`length(T ∪ T)`" should be `length(T ∪ T′)`. In line 9 of `Π_oBC`, "`(v′, P′)`" should be `(v, P′)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's Byzantine message-passing model `Cslib.Byzantine.PartialSync`. Time is discrete; parties are
  deterministic state machines; the adversary chooses a static Byzantine set, their messages, the GST
  and all delivery times. Signatures are CSLib's abstract unforgeable tokens: the adversary may emit
  only its own tokens or tokens already sent by honest parties (`Run.AuthValid`).
* *Synchronous network:* `gst = 0`, delays `≤ δ`, and at most `tₛ` faults (`syncRuns`). *Asynchronous
  network:* at most `tₐ` faults and arbitrary finite delays, with no bound at all (`asyncRuns` = library
  `Run.AsyncValid`, *unbounded* asynchrony; explicit form `asyncRuns_iff`). All parties step every tick,
  so their clocks are synchronized.
* **Impossibility:** the theorem is stronger than the paper's. It needs security only on synchronous
  runs and on *partially synchronous* runs (`psyncRuns`), and inputs only from a domain containing two
  points at distance `> ε`. It covers every signature scheme (`Auth`) and arbitrary message and state
  types. The adversary is static, while the paper's is adaptive. Protocols are deterministic, as in the
  paper.
* **Counterexamples:** `Π_rBC`, `Π_oBC` and `Π_AA` with `S = 1` are encoded line by line (`RBC.lean`,
  `OBC.lean`, `AA.lean`). A message produced at time `kΔ` is processed at `(k+1)Δ` (`Δ` = one tick,
  delay `0`). Messages that arrive at the same time are processed before the time-triggered actions.
  FIFO channels use sequence numbers, as the paper suggests. The attack runs are synchronous
  executions of the paper's model in which every honest message takes exactly `Δ`. The runs are
  computed by `decide` with Boolean values and transferred to real values by an equivariance lemma
  (the broadcast layers only compare values for equality).
* **Iteration analysis:** abstract. The `i`-th call of `Π_oBC` is a partial map "sender ↦ value" per
  party, satisfying the synchronous (`SyncOBC`) or asynchronous (`AsyncOBC`) guarantees of
  Definition 2.2.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5.1 (`2tₛ + tₐ ≥ n` ⇒ no hybrid AA; `n ≥ 2`) | `theorem_5_1`, `theorem_5_1'`, strong form `not_secure_sync_and_psync` | `Impossibility.lean` |
| Theorem 5.1 for `n = 1`: **false** | `theorem_5_1_false_n_eq_one` | `Impossibility.lean` |
| Lemma 3.7 (ranges of `T`, `T′` intersect) | `lemma_3_7` | `Trim.lean` |
| Lemma 3.6 | `lemma_3_6`, `lemma_3_6'` | `Trim.lean` |
| Line 7 of `Π_AA` = midpoint of the kept values of any MSR trimming (CSLib `IsTrim`) | `trim_eq_of_isTrim`, `midTrim_eq_of_isTrim` | `Trim.lean` |
| Lemmas 3.2–3.3 (one synchronous iteration) | `step_sync` | `Iteration.lean` |
| Lemmas 3.4–3.5 (one asynchronous iteration) | `step_async` | `Iteration.lean` |
| Theorem 3.1, *relative to Definition 2.2* (validity, `ε`-agreement after `S` iterations, `S = ⌈log₂(δmax/ε)⌉` suffices) | `theorem_3_1_sync`, `theorem_3_1_async`, `le_two_pow_ceil_logb` | `Iteration.lean` |
| Theorem 4.1 (`Π_rBC` synchronized consistency): **false** | `RBC.rbc_not_syncConsistent` | `RBC.lean` |
| Theorem 3.1 (1) (`Π_AA` secure in sync): **false** | `AA.theorem_3_1_sync_false` | `AA.lean` |

**Not formalized.** The asynchronous guarantees of `Π_rBC` and `Π_oBC` (the asynchronous parts of
Theorem 4.1 and Lemmas 4.5–4.7) are not formalized, so Theorem 3.1 (2) is verified only relative to
Definition 2.2 plus authenticity. The same holds for multi-iteration `Π_AA` (`S > 1`) as a concrete
protocol, for message complexity, and for the general-`n` version of the `Π_rBC` attack (argued above,
not formalized).

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Sanity checks of the encodings: with an honest sender, `Π_rBC` delivers the sender's
value to everybody at `3Δ` (`RBC.rbc_honest_sender`). With a silent Byzantine party, `Π_AA` terminates
and both honest parties output `1/2` (`AA.aa_silent`). The impossibility hypotheses are satisfiable:
for `n = 1` the trivial protocol meets them (`outputInput_secure`). CSLib modules used:
`Byzantine/PartialSync/{Model,Auth,Constructions,Sync}`, `ApproxConsensus/Trim`. Shared library code
(`Cslib/Computability/Distributed/Byzantine/PartialSync/`): the run classes `Run.SyncValid`, `Run.Valid`, `Run.AsyncValid` (`RunClasses.lean`),
quiet runs `Run.quiet` (`Runs.lean`), `Run.st_map` (states of runs commute with maps of messages, states
and inputs, `Map.lean`), `Run.st_eq_simStates` (memoised state computation of zero-delay runs, for
`decide`-checked concrete executions, `Sim.lean`), and the labelling lemma `Fintype.exists_labelling`
(`Cslib/Foundations/Combinatorics/Labelling.lean`).
