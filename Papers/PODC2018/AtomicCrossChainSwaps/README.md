# Atomic Cross-Chain Swaps — PODC 2018

Maurice Herlihy. *Atomic Cross-Chain Swaps.* PODC 2018. DOI
[10.1145/3212734.3212736](https://doi.org/10.1145/3212734.3212736). Formalized version: arXiv
[1801.09515](https://arxiv.org/abs/1801.09515) v4 (the latest); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The protocol of §4.5, as specified, violates its safety theorem
(Theorem 4.9): on the paper's own three-party example a 2-party coalition leaves a conforming
leader Underwater. It also violates its liveness theorem (Theorem 4.7) with the stated timeouts:
on the same example nothing is triggered even when everyone conforms. Both fixes are small: the
standard HTLC deadline guard on secret release, and one extra `Δ` in the timeouts. The repaired
protocol is proved safe, live (within `2·diam(D)·Δ`) and atomic. The theory of §3 is correct: a
uniform protocol is atomic iff `D` is strongly connected, or in general iff reachability is
symmetric.

## Mistakes in the paper

* **Theorem 4.9 is false: a conforming leader can end Underwater.** Lemma 4.8's proof says: "if
  `v` appears in `p`, then `v` has already received (and signed) a hashkey that triggers `h` on
  `(u, v)`." For a leader's own hashlock this fails. A leader releases its secret whenever its
  last entering contract appears, even if its own key has already expired. Its failed `unlock`
  call is public, since the pseudocode's `unlock` does not revert. Colluders then extend the
  signed secret along a longer path, whose key expires later. On the §1 example, Bob and Carol rob
  Alice this way. Carol publishes `C → A` at the last moment, Alice's call fails, and Bob presents
  `(B, C, A)` on `A → B`. The counterexample uses timeouts already enlarged as in the next item,
  and no front-running. (`literal_unsafe_late`)
  **Repair:** the standard HTLC guard. A leader releases only if its own hashkey still meets its
  deadline. With it, no conforming party is ever Underwater, for any digraph, any leaders, any
  timeouts and any coalition. (`Setting.safety`)
  *Ambiguity, not an error.* A leader publishes its leaving contracts first and may see a foreign
  hashlock unlocked while still in Phase One. Suppose it then forwards that key once, to the
  entering contracts present at that moment. Then a single deviator can rob it on Figure 7's
  digraph (`literal_unsafe_refwd`). The proof of Theorem 4.9 says that a leader issues hashkeys
  only in Phase Two, after all its entering contracts exist; under that reading the attack
  disappears. Our repaired protocol implements this intended behaviour: it keeps forwarding to
  entering contracts that appear later.
* **Theorem 4.7 / Lemma 4.6 are false as stated: the hashkey timeouts are one `Δ` short.** A
  hashkey expires at `(diam(D) + |p|)Δ`. A leader's own key has `|p| = 0`, but the leader may
  present it only after Phase One, which itself may take `diam(D)·Δ`. On the three-party example
  of §1, with the timing of Figures 1–2, nothing is triggered when everybody conforms. This holds
  whether `diam = 3`, as the example's own timeouts imply, or `diam = 2`, the longest path between
  distinct vertices. So the protocol is not even uniform. Timeouts `(diam + 1 + |p|)Δ` fix it, as
  in the single-leader formula of §4.6. Then every arc is triggered by `2·diam(D)·Δ`, as claimed.
  (`literal_not_live`; repaired: `Setting.theorem_4_7`)
* **Lemma 4.13 needs simple paths.** The paper's paths may repeat their last vertex anywhere
  ("lassos"). Then the longest path from `w` to the leader may pass through `v`, and
  `D(v, v̂) ≥ D(w, v̂) + 1` fails. Five arcs on four vertices suffice. With simple paths the lemma
  holds. (`Lasso.not_lemma_4_13_lax`; `lemma_4_13`) Conversely, the contracts *need* the paper's
  lax paths. If `isPath` accepted only simple paths and cycles, a deviating leader could present a
  cycle key that conforming parties cannot extend. Our model checker found this; it is not in Lean.
* **Theorem 3.5 needs `D` connected**, which §3 assumes "without loss of generality". On two
  disjoint 2-cycles there is a uniform atomic protocol. The exact characterization, valid for all
  digraphs, is: atomic iff reachability is symmetric. (`theorem_3_5_needs_connected`,
  `SwapGame.atomic_iff`)
* **Proof gaps, statements true.** Lemma 3.4 silently assumes that coalitions can withhold their
  assets; we make this an explicit hypothesis and prove it for the protocol. Lemma 4.8 needs an
  unforgeability argument: a party's first observed key does not contain the party itself.
  (`Setting.game_canAbstain`, `Setting.not_mem_first`)
* **Small slips.** In Lemma 3.4 the coalition gets Discount, not FreeRide (it has no entering arcs).
  `refund()` should test "not unlocked and timed out". Lemma 4.14's proof cites itself. The
  abstract (space `O(|A|²)`) and §1 (communication `O(|A|·|L|)`) disagree. `diam` is the
  longest-path length, so "time `O(diam(D))`" can mean `Θ(|V|)`.

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
* The single-leader timelock protocol as an execution (only its timeout arithmetic, Lemma 4.13).
* Lemma 4.11 for an undefined class of "hashed-timelock protocols".
* Executions with variable latency below `Δ`.
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
