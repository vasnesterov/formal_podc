# Atomic Cross-Chain Swaps — PODC 2018

Maurice Herlihy. *Atomic Cross-Chain Swaps.* PODC 2018. DOI
[10.1145/3212734.3212736](https://doi.org/10.1145/3212734.3212736). Formalized version: arXiv
[1801.09515](https://arxiv.org/abs/1801.09515) v4 (the latest); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** As printed, the protocol of §4.5 violates its safety theorem (Theorem 4.9: on the paper's
own three-party example a 2-party coalition leaves a conforming leader Underwater) and its liveness theorem
(Theorem 4.7: on the same example nothing is triggered even when everyone conforms). Both fixes are small, the
standard HTLC deadline guard on secret release and one extra `Δ` in the timeouts, and the repaired protocol is proved
safe, live (within `2·diam(D)·Δ`) and atomic; the theory of §3 also holds: a uniform protocol is atomic iff `D` is
strongly connected, or in general iff reachability is symmetric. The impossibility when `L` is not a feedback vertex
set was checked only for this protocol, not for all hashed-timelock protocols.

## Mistakes in the paper

### 🔧 Theorem 4.9 and Lemma 4.8 (safety: no conforming party ends Underwater)
On the §1 three-party example, Bob and Carol rob a conforming leader Alice: she releases her secret
after her own key has expired, and they extend the signed secret along a longer path whose key
expires later (`literal_unsafe_late`).

**Impact.** The protocol as specified is unsafe.

**Details.** Lemma 4.8's proof says: "if `v` appears in `p`, then `v` has already received (and
signed) a hashkey that triggers `h` on `(u, v)`." For a leader's own hashlock this fails. A leader
releases its secret whenever its last entering contract appears, even if its own key has already
expired. Its failed `unlock` call is public, since the pseudocode's `unlock` does not revert.
Colluders then extend the signed secret along a longer path, whose key expires later. On the §1
example, Carol publishes `C → A` at the last moment, Alice's call fails, and Bob presents
`(B, C, A)` on `A → B`. The counterexample uses timeouts already enlarged as in the next item, and
no front-running.

*Ambiguity, not an error.* A leader publishes its leaving contracts first and may see a foreign
hashlock unlocked while still in Phase One. Suppose it then forwards that key once, to the entering
contracts present at that moment. Then a single deviator can rob it on Figure 7's digraph
(`literal_unsafe_refwd`). The proof of Theorem 4.9 says that a leader issues hashkeys only in
Phase Two, after all its entering contracts exist; under that reading the attack disappears. Our
repaired protocol implements this intended behaviour: it keeps forwarding to entering contracts
that appear later.

**Repair.** The standard HTLC guard: a leader releases only if its own hashkey still meets its
deadline. Then no conforming party is ever Underwater, for any digraph, any leaders, any timeouts
and any coalition (`Setting.safety`), and the protocol is atomic (`Setting.game_atomic`).

### 🔧 Theorem 4.7 and Lemma 4.6 (liveness: hashkey timeouts one `Δ` short)
On the §1 three-party example with the timing of Figures 1–2, nothing is triggered even when
everybody conforms, because a leader's own key (`|p| = 0`) expires before the leader may present it
(`literal_not_live`).

**Impact.** The protocol is not even uniform as specified.

**Details.** A hashkey expires at `(diam(D) + |p|)Δ`. A leader's own key has `|p| = 0`, but the
leader may present it only after Phase One, which itself may take `diam(D)·Δ`. This holds whether
`diam = 3`, as the example's own timeouts imply, or `diam = 2`, the longest path between distinct
vertices.

**Repair.** Timeouts `(diam + 1 + |p|)Δ`, as in the single-leader formula of §4.6; then every arc
is triggered by `2·diam(D)·Δ`, as claimed (`Setting.theorem_4_7`).

### 🔧 Lemma 4.13 (needs simple paths)
Under the paper's own path definition, which lets a path repeat its last vertex anywhere ("lassos"),
the longest path from `w` to the leader may pass through `v`, and `D(v, v̂) ≥ D(w, v̂) + 1` fails
on five arcs on four vertices (`Lasso.not_lemma_4_13_lax`).

**Impact.** It only concerns the timeout arithmetic of the single-leader protocol of §4.6.

**Details.** Conversely, the contracts *need* the paper's lax paths. If `isPath` accepted only
simple paths and cycles, a deviating leader could present a cycle key that conforming parties
cannot extend. Our model checker found this; it is not in Lean.

**Repair.** With simple paths the lemma holds (`lemma_4_13`, `timeout_gap`).

### ✏️ Slips
- Theorem 3.5 and the abstract need `D` connected: on two disjoint 2-cycles there is a uniform atomic protocol,
  although `D` is not strongly connected (`theorem_3_5_needs_connected`). §3 assumes connectivity "without loss of
  generality". The exact characterization, valid for all digraphs, is: atomic iff reachability is symmetric
  (`SwapGame.atomic_iff`).
- §2.1: the side condition of `v + p` ("does not include the arc `(v, u₀)`") should say that `p` does not include `v`.
- `refund()` should test "not unlocked and timed out".
- In the proof of Lemma 3.4 the coalition gets Discount, not FreeRide (it has no entering arcs).
- The proof of Lemma 3.4 silently assumes that coalitions can withhold their assets. We make this an explicit
  hypothesis and prove it for the protocol (`Setting.game_canAbstain`).
- The proof of Lemma 4.8 needs an unforgeability argument: a party's first observed key does not contain the party
  itself. True for the repaired protocol; proved (`Setting.not_mem_first`).
- The abstract (space `O(|A|²)`) and §1 (communication `O(|A|·|L|)`) disagree.

### Typos
- Lemma 4.14's proof cites itself; it should cite Lemma 4.13.
- §4.3 cites the `require` of `claim()` as Line 36, which belongs to `refund()`.
- `diam` is the longest-path length, so "time `O(diam(D))`" can mean `Θ(|V|)`.
- §4.5 does not say when a leader still in Phase One forwards foreign keys; see the ambiguity under Theorem 4.9.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Swap digraph: a Mathlib `Digraph` on a finite type. Paths follow §2.1 (all vertices except
  possibly the last are distinct). `diam` = length of a longest path, cycles included (matches
  the §1 example). Reachability, strong connectivity, walks of bounded length and the follower
  subgraph are the shared notions of `Cslib/Foundations/Combinatorics/Digraph/Walk.lean` (`Digraph.Reachable`,
  `Digraph.StronglyConnected`, `Relation.RelatesWithinSteps`, `Digraph.deleteVerts`).
* Outcome: the set of eventually triggered arcs; the five payoff classes are taken literally. A
  protocol is abstracted as a `SwapGame`: for each deviating coalition, its possible outcomes.
  Strong Nash means no deviating coalition gets FreeRide or Discount.
* Execution model of §4, in `Protocol.lean`:
  * Timing is synchronous: discrete time in units of `Δ`, conforming actions land exactly one `Δ`
    later (Figures 1–2), and deadlines are inclusive.
  * One correct contract per arc, one hashlock per leader. A hashkey is the path `p` from the
    counterparty to the leader; it is valid until `B + |p|` (the paper: `B = diam`).
  * The deviating coalition is arbitrary and shares knowledge. It knows its own leaders' secrets
    and every key ever submitted (even in failed calls), with all inner signatures. It can sign
    only as its own members.
  * Two adversary settings: with and without front-running.
  * Two protocol variants: the literal one (`fixed = false`) and the repaired one (`fixed = true`).
  * Conforming parties follow §4.5 exactly. The scheduler resolves the only nondeterminism, which
    key to adopt first.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| payoff classes, acceptable = ¬Underwater | `not_underwater_iff` | `Atomicity.lean` |
| Lemma 3.3 | `SwapGame.atomic_of_uniform` | `Atomicity.lean` |
| Lemma 3.4 | `SwapGame.not_strongNash` | `Atomicity.lean` |
| Theorem 3.5 (connected `D`) / exact form | `SwapGame.atomic_iff_stronglyConnected` / `SwapGame.atomic_iff` | `Atomicity.lean` |
| Theorem 3.5 without connectivity: false | `theorem_3_5_needs_connected` | `Atomicity.lean` |
| Lemma 4.1 | `exists_fired_iff` | `Pebble.lean` |
| Lemmas 4.2, 4.3 | `reachIn_diam`, `fired_diam` | `Pebble.lean` |
| Lemma 4.5 | `Setting.con_of_fired` | `Liveness.lean` |
| Lemma 4.6, Theorem 4.7 (repaired timeouts) | `Setting.liveness`, `Setting.theorem_4_7` | `Liveness.lean` |
| Theorem 4.7 with the paper's timeouts: false | `literal_not_live` | `Counterexamples.lean` |
| Lemma 4.8 (repaired protocol) | `Setting.forward` | `Safety.lean` |
| Theorem 4.9 (repaired protocol) | `Setting.safety` | `Safety.lean` |
| Theorem 4.9 for the literal protocol: false / forward-once ambiguity | `literal_unsafe_late` / `literal_unsafe_refwd` | `Counterexamples.lean` |
| main claim: the protocol is uniform / atomic (repaired) | `Setting.game_uniform`, `Setting.game_atomic` | `Main.lean` |
| Theorem 4.12 (core; for this protocol) | `no_contract_on_follower_cycle`, `Setting.not_live_of_not_isFVS` | `Pebble.lean`, `Main.lean` |
| Lemma 4.13 (simple paths) / with lax paths: false | `lemma_4_13`, `timeout_gap` / `Lasso.not_lemma_4_13_lax` | `SingleLeader.lean` |

**Not formalized.**
* The space bound (Theorem 4.10).
* The single-leader timelock protocol as an execution, including Lemma 4.14 (only its timeout arithmetic,
  Lemma 4.13). It seems to inherit the late-release problem of Theorem 4.9, but the repair is not proved for it.
* Lemma 4.11 and Theorem 4.12 for an undefined class of "hashed-timelock protocols". Only the core for this protocol
  is proved; whether the others can really collude to trigger `(v, w)`, given that keys are signed along paths
  through `v`, was not investigated.
* The claim that assets are refunded by `T + 2·diam·Δ` when parties deviate. With the repaired timeouts the latest
  expiry is `(2·diam + 1)Δ`.
* Executions with variable latency below `Δ`, including the attack variant without public failed calls.
* The "simple paths and cycles" reading of the contracts' path check (model-checked only).

**Trust.** Model limitations:
* Timing is lock-step: every conforming action takes exactly `Δ`.
* The adversary does not control latencies within `Δ`, so the safety proof covers only that
  setting.
* The model-checking claim below is informal.

No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexamples are checked by kernel computation (`decide +kernel`) on the
executable model, including admissibility of the adversary's schedule for all times.
Non-vacuity: every coalition has an admissible schedule (`Setting.idleSched_valid`), and the
three-party example satisfies all hypotheses of `Setting.game_atomic` (example in `Main.lean`).
The infrastructure is self-contained (Mathlib only). A bounded Python model checker of the same
model ([`modelcheck/`](modelcheck/), run under a memory cap) was used to find the counterexamples. On the repaired protocol it searched 323 instances: strongly
connected digraphs with 3 vertices, all leader sets and coalitions, `B ∈ {3, 4}`, with
front-running. It completed 316 of them and found no attack; the other 7 hit its state cap. It is not part of the
development.
