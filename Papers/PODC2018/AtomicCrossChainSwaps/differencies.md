# Differences between the formalization and the paper

Paper: M. Herlihy, *Atomic Cross-Chain Swaps*, PODC 2018 (arXiv 1801.09515v4, the latest version;
numbering follows it). Lean namespace `AtomicSwap`.

Classification: **false statement**, **false only in a degenerate case**, **proof gap (statement
true)**, **under-specified definition**, **typo**, **modelling choice**.

## Errors in the paper

1. **Theorem 4.7 / Lemma 4.6 are false as stated (off-by-one in the hashkey timeouts). False
   statement, easy fix.** A hashkey `(s, p, σ)` expires at `(diam(D) + |p|)Δ`. Phase One alone
   can take `diam(D)Δ` (Lemma 4.5), and only then does a leader present its own key `(s, (ℓ), σ)`.
   That key has `|p| = 0`, so it is already expired, or expires the instant it is presented. On the
   paper's own three-party example (`A → B → C → A`, leader `A`), with the timing of Figures 1–2
   (each step takes `Δ`, and triggering at exactly the timeout counts), `diam = 3`. Then Alice's
   key expires at `3Δ`, but Carol's contract only appears at `3Δ`, so Alice presents the key at
   `4Δ`. If everybody conforms, *nothing* is triggered: everyone ends NoDeal, not Deal, so the
   protocol is not uniform. The same holds if `diam` is read as "longest path between distinct
   vertices" (`= 2`). (`literal_not_live`)
   With one more `Δ` (expiry `(diam + |p| + 1)Δ`, as in the single-leader formula of §4.6)
   everything works, and the paper's bound holds: all arcs are triggered by `2·diam(D)·Δ`
   (`Setting.theorem_4_7`, `literal_live_four`). The exact condition is `B ≥ K + 2`, where `K` is
   the number of rounds of the lazy pebble game (`Setting.liveness`).
   *Conventions.* Whether exactly one `Δ` is missing depends on boundary conventions the paper
   does not fix. One choice is when leaders publish relative to the start `T`. Another is whether
   the deadline check is strict (`now < start + …`, as in the pseudocode) or inclusive (as in
   Figure 2). Suppose leaders' contracts are already on chain at `T` and the check is inclusive.
   Then `B = diam` is exactly tight. With the pseudocode's strict check it fails again. We use the
   conventions of Figures 1–2.

2. **Theorem 4.9 is false for the protocol as written: a conforming leader can end Underwater
   (2-party coalition on the §1 example). False statement.** Lemma 4.8's proof says: "If `v`
   appears in `p`, then `v` has already received (and signed) a hashkey that triggers `h` on
   `(u, v)`." This fails for a leader's own hashlock, because that key may already have expired.
   * *Late release.* A leader releases its secret as soon as all its entering contracts exist, and
     never checks the clock. If the last entering contract appears too late, the leader's own
     unlock call fails. But the call is on a public ledger, and it reveals `s` and `sig(s, ℓ)`. A
     coalition can extend this to a longer path, whose hashkey expires later, and collect the
     leader's outgoing asset. Counterexample: the three-party example with timeouts
     `(diam + 1 + |p|)Δ` and coalition `{B, C}`, no front-running. Carol publishes `C → A` at `4Δ`.
     Alice's unlock lands at `5Δ`, past her deadline `4Δ`. Bob presents `(s, (B, C, A), …)`, valid
     until `6Δ`, on `A → B`. (`literal_unsafe_late`)
     The pseudocode's `unlock` does not revert, so failed calls are recorded on chain; this is why
     we model them as public. If conforming calls may land at different times within `Δ`, the
     attack works even without public failed calls: one of the leader's unlocks succeeds and
     another fails. This variant is not formalized.

   **Repair** (`fixed = true` in `Protocol.lean`). (a) A leader releases its secret only if its
   own hashkey can still meet its deadline (`t + Δ ≤ T + BΔ`); this is the standard HTLC guard.
   (b) Forwarding is repeated for entering contracts that appear later, while the forwarded key is
   still valid. This is the behaviour the paper intends (see item 2a). With both changes,
   no conforming party ends Underwater. This holds for every digraph, every set of leaders (not
   necessarily a feedback vertex set), every `B` and every coalition, even a front-running one
   (`Setting.safety`). With `B ≥ diam + 1` the repaired protocol is uniform and atomic
   (`Setting.game_uniform`, `Setting.game_atomic`).

2a. **When a leader forwards foreign keys. Under-specified (ambiguity, not an error).**
   A leader publishes its leaving contracts
     first. It can therefore see a foreign hashlock `h_i` unlocked on a leaving arc *before* all its
     entering arcs have contracts. The protocol forwards "the first time … at each entering arc's
     contract". It forwards only once, so an entering contract that appears later never gets
     `h_i` unlocked. Counterexample: Figure 7's digraph (complete digraph on `A, B, C`, leaders
     `A, B`), with timeouts already fixed to `(diam + 1 + |p|)Δ`. `A` alone deviates, with no
     front-running. `A` unlocks `h_A` on `B → A` with her bare secret before publishing `A → B`.
     `B` forwards to `C → B` only. Then `A` publishes `A → B`, `B` releases `s_B`, and `A` collects
     `B → A`. `A → B` is never triggered, so `B` is Underwater. (`literal_unsafe_refwd`)
   This reading has a leader forward a foreign key while still in Phase One. But the proof of
   Theorem 4.9 says that "a leader issues hashkeys in Phase Two only after a contract has been
   published on every entering arc". Under that reading the attack disappears, so this is not
   counted as a mistake. The repaired protocol implements the intended behaviour.

3. **Lemma 4.8's proof also omits an unforgeability step. Proof gap (statement true for the
   repaired protocol).** The case "`v` does not appear in `p`" needs that the *first* key `v`
   observes does not contain `v`. This holds because `v`'s signature cannot be forged and `v`
   signs only after its first observation. We prove it (`Setting.known_good`,
   `Setting.not_mem_first`).

4. **The meaning of "path" matters for the contracts, and the paper's own definition is the one
   that works. Under-specified definition.** §2.1 defines a path as a sequence whose vertices
   *except possibly the last* are distinct. This allows cycles and also "lassos" whose last vertex
   repeats an inner one. With this definition `v + p` is a path whenever `v ∉ p`, which Lemma 4.8
   needs. Suppose instead the contract's `isPath` accepts only simple paths and cycles. Then even
   the repaired protocol is unsafe. A deviating leader `ℓ` presents a cycle key `(ℓ, x, ℓ)`, the
   conforming forwarder's `v + p = (v, ℓ, x, ℓ)` is rejected, and `v` cannot unlock its entering
   arcs. Our Python model checker found this on the complete digraph on 3 vertices. It is not in
   Lean. The paper's side condition for `v + p` ("`p` does not include the arc `(v, u₀)`") seems to
   mean "`p` does not include `v`", which is what we use. We formalize the paper's literal (lax)
   definition (`IsPath`).

5. **Lemma 4.13 is false under the paper's own path definition. Under-specified definition.** With
   lassos allowed, the longest path from a follower `w` to the single leader can be a lasso that
   passes through the leader and then through `v`. Then `D(v, v̂) ≥ D(w, v̂) + 1` fails.
   Counterexample: arcs `0→1, 1→2, 2→0, 1→3, 3→0`, leader `0`. The lax-path distance from `2` to `0`
   is `4`, via `(2, 0, 1, 3, 0)`, but from `1` to `0` it is only `2`.
   (`Lasso.not_lemma_4_13_lax`) With simple paths the lemma holds (`lemma_4_13`, `timeout_gap`).

6. **Theorem 3.5 needs `D` to be (weakly) connected. False only in a degenerate case.** §3 assumes
   connectivity "without loss of generality". Without it, the "only if" half fails. On two disjoint
   2-cycles there is a uniform, atomic protocol even though `D` is not strongly connected
   (`theorem_3_5_needs_connected`). The exact statement holds for every digraph: a uniform protocol
   in which coalitions can withhold their assets is atomic iff reachability is symmetric
   (`SwapGame.atomic_iff`).

7. **Lemma 3.4's proof mislabels the payoff. Typo-level.** The coalition `X` of vertices not
   reachable from `y` has no entering arcs. When it withholds its assets it gets Discount (and
   NoDeal), not FreeRide. The conclusion is unaffected (`SwapGame.not_strongNash`).

8. **Lemma 3.4 uses an unstated modelling assumption. Proof gap.** A deviating coalition can
   always refuse to give away its assets. We make it an explicit hypothesis (`CanAbstain`) and
   prove that the HTLC protocol satisfies it (`Setting.game_canAbstain`, which needs `L ≠ ∅`:
   with no hashlocks every arc counts as triggered).

9. **Typos and small slips.**
   * `refund()` (Line 37): "if (any hashlock unlocked and timed out)" should be "not unlocked".
   * §4.3 cites the `require` of `claim()` as Line 36; that line belongs to `refund()`.
   * Lemma 4.14's proof cites Lemma 4.14 itself; it should cite Lemma 4.13.
   * The abstract states space complexity `O(|A|²)`, while §1 states communication complexity
     `O(|A|·|L|)`.
   * `diam(D)` is the length of a *longest* path. This is NP-hard to compute and is often close to
     `|V|`, not the usual diameter. So "time complexity `O(diam(D))`" should be read with this in
     mind.

## Modelling choices and definitions

* **Digraphs.** Mathlib `Digraph V` on a finite vertex type; loops are allowed (harmless).
  `IsPath` is the paper's §2.1 path. `diam D` is the supremum of the lengths of all paths, cycles
  included. This is the reading consistent with the §1 example (`diam = 3` for the 3-cycle, timeouts
  `6Δ, 5Δ, 4Δ = (diam + D(v, v̂) + 1)Δ`). The text's "from any vertex to any other" would give `2`.
  Under-specified definition; our counterexamples cover both readings.
* **Outcomes.** An outcome is the set of eventually triggered arcs. The five payoff classes are
  defined literally. FreeRide and Discount overlap (all entering arcs triggered, no leaving arc
  triggered). Acceptable = not Underwater (`not_underwater_iff`).
* **Protocols as games.** Definitions 3.1 and 3.2 are stated for an abstract `SwapGame`: for each
  deviating coalition, the set of possible outcomes. "Strong Nash" means no deviating coalition
  gets FreeRide or Discount. This is the reading of the proof of Lemma 3.3, and it is stronger
  than the Pareto-dominance reading of Figure 3. Lemma 3.3 is proved under symmetric reachability
  and uses only the no-Underwater clause. The paper's remark that each individual member of `X`
  also does at least as well as Deal is not formalized.
* **Time.** Discrete, unit `Δ`, start at `0`. Everybody observes all chains at integer times. A
  conforming party's action submitted at time `t` lands at `t + 1` (lock-step), as in Figures 1–2.
  A leader's first contracts land at `Δ`. A call succeeds iff it lands no later than the key's
  deadline `B + |p|` (inclusive). The paper uses `B = diam D`. The safety proof uses only "lands
  within `Δ`", but it is formalized for the lock-step model only.
* **Contracts.** Only correct contracts are modelled; a conforming party treats an incorrect one as
  missing. Every arc carries one hashlock per leader. An arc is triggered when all its hashlocks
  are unlocked. `claim` has no deadline and `refund` is implicit.
* **Adversary.** The coalition shares knowledge. It knows the secrets of its own leaders and every
  key ever submitted (including failed calls) together with all suffixes, i.e. the inner
  signatures. It can sign as any of its members but never as a conforming party (symbolic,
  unforgeable signatures). It publishes its own contracts whenever it likes, or never, and calls
  `unlock` on arcs it is the counterparty of. With `rush = true` it can use keys that conforming
  parties submit in the same round (front-running). Safety is proved for both settings; the
  counterexamples use no front-running.
* **Tie-breaking.** When several leaving arcs show a hashlock unlocked for the first time, the
  schedule chooses which key a conforming party adopts (`Moves.pick`). The theorems hold for every
  choice.
* **Market clearing (§4.2)**, the broadcast optimisation and the recurrent variant (§5) are not
  modelled.

## Results formalized as stated (or with the repairs above)

* Lemma 3.3 (`SwapGame.atomic_of_uniform`), Lemma 3.4 (`SwapGame.not_strongNash`), Theorem 3.5
  (`SwapGame.atomic_iff_stronglyConnected`).
* Lemma 4.1, both directions (`exists_fired_iff`). Lemma 4.2/4.3: every vertex fires by round
  `diam − 1` and all distances are `≤ diam − 1` (`fired_diam`, `reachIn_diam`). This gives
  Lemma 4.5 (`Setting.con_of_fired`) and the bound `2·diam·Δ` of Theorem 4.7 for the repaired
  timeouts.
* Theorem 4.12, waits-for core: an arc on a cycle of followers never gets a contract
  (`no_contract_on_follower_cycle`). Consequently, if `L` is not a feedback vertex set, the
  protocol fails even when all parties conform (`Setting.not_live_of_not_isFVS`). Lemma 4.11 and
  "any uniform swap protocol based on hashed timelocks" are not formalized, since that class of
  protocols is not defined. Note that with hashkeys, "the others collude to trigger `(v, w)`"
  (Lemma 4.11's proof) is not automatic, because keys must be signed along paths that may pass
  through `v`. We have not investigated this further.
* Lemma 4.13 with simple paths (`lemma_4_13`, `timeout_gap`).

## Not formalized

* Theorem 4.10 (space `O(|A|²)`) and other bit counting.
* The single-leader timelock protocol (§4.6) as an execution: only the timeout arithmetic
  (Lemma 4.13) is formalized. Lemma 4.14 inherits the late-release problem of item 2: with plain
  timeouts the bare secret suffices, so a leader that releases late can be robbed.
* The claim that assets are refunded by `T + 2·diam·Δ` when parties deviate. With the repaired
  timeouts the latest expiry is `(2·diam + 1)Δ`.
