# Differences between the formalization and the paper

Rules R1–R6 refer to `.claude/skills/formalize-paper/verdicts.md`.

## Statement-level issues

1. **Lemma 2 is false for `v = Lᵢ` when the leader withholds its secret** (R1: numbered lemma; classed ⚠️ by R3).
   - Counterexample: `TwoCycle.lemma_2_false` (digraph `A ⇄ B`, leader `A`, Bob deviating, `p = 1`). Alice's net
     redemption-premium profit is `−1`. She escrowed one asset, and her key never appears on her leaving arc.
   - True versions: `lemma_2` for `v ≠ Lᵢ`, and `lemma_2_leader_released`.
   - *Borderline call.* We class it ⚠️ (imprecise statement, intent recoverable), not ❌. The proof of Lemma 3
     explicitly pays the leader's own redemption premiums `R(Lᵢ)` out of the escrow premium `E(u, v) = R(Lᵢ)`, and
     only then applies Lemma 2 to the leader. So the paper's own accounting excludes the leader's own deposits from
     "net redemption premium profit" in this case, and the fix is local. A stricter reader could call Lemma 2 a
     false numbered lemma (❌). The hedging result (Lemma 6) is unaffected either way.
2. **Lemma 3, in its split form, is false for leaders** (same reason, same R3 call).
   - Counterexample: `TwoCycle.lemma_3_split_false`. The net escrow profit is `2`, the net redemption profit `−1`,
     against the claimed `≥ 1`. The total is `1`.
   - We prove the total form: escrow profit `≥ 0` and total premium profit `≥ p` per escrowed asset (`lemma_3`).
     When an entering asset is missing, every asset `v` escrowed stays unredeemed, which is why "escrowed" suffices
     here.
3. **Equation (1).** For `v ∥ q` that is neither a path nor a cycle (`v` strictly inside `q`), the paper's
   recursion does not terminate. Such premiums do occur with ≥ 2 leaders. We set `R(q, v) = p` there. This is the
   only value the protocol needs, since a conforming `v` does not extend `q`. Classed R3: the paper's
   well-definedness remark shows it intends recursion over paths only.
4. **Lemma 1** says "if a swap completes successfully, then each `v` has all its premiums refunded". We prove it
   for executions where everybody conforms and every asset is escrowed (`lemma_1`, `lemma_1_net`).
   - With deviators it can fail for a conforming `v`, in a harmless way. Suppose a deviating `w` deposits a
     premium on `(v, w)` with a short path, and later presents a valid key with a longer path, after the premium's
     deadline. Then `v` forwards too late for its own premium's deadline and pays it, but it collects `w`'s premium
     on `(v, w)`, which covers it plus `p`.
   - We read Lemma 1 as a statement about the normal case where everybody conforms (the paper states it just
     before "What can go wrong?", mirroring the liveness property of §5.2), so this is not counted as an error.
     The scenario also depends on our choice of premium deadlines, which the paper does not fix. It is not
     formalized. (The paper's sentence "In the following lemmas, `v` is a compliant party" precedes Lemma 1.)
5. **Lemma 6's proof** says "a profit of at least `p` for that asset" for every escrowed asset. That holds only
   for assets that are not redeemed (Definition 1). We prove `p · |unredeemed escrowed assets| ≤ net` (`lemma_6`),
   and `net ≥ 0` always (`net_nonneg`).
6. **Lemma 7** needs at least one conforming bidder, which the paper leaves implicit. Without one it fails
   (`Auction.lemma7_needs_compliant_bidder`). Classed R4: Lemma 8 only uses it for a conforming bidder.

## Protocol details we had to fix (under-specification, R4)

- **Timeouts (§7.1).** The paper says only "each step takes time at most `Δ` … each following step's timeout
  increases by `Δ`". We use the family `Swap`:
  - escrow-premium deadlines `dl1 v ≤ t1`;
  - redemption premiums with path `q` by `t1 + |q|` (`|q|` = number of vertices);
  - activation at `t2 ≥ t1 + |V|`;
  - asset deadlines `dl3` with `dl3 u + 1 ≤ dl3 v` along arcs into followers, and `t2 + 1 ≤ dl3 v ≤ B`;
  - keys and redemption premiums with path `q` expire at `B + |q|`.

  The hashkey timeout `(diam(G) + |q|)Δ` of the base protocol is replaced by `B + |q|`, because the base protocol
  now starts after two premium phases. The constraints are used in the proofs: the follower slack is what lets a
  follower pass escrow premiums through, and `B ≥ dl3` is what lets a leader's key meet its deadline.
- **Followers escrow only on activated arcs.** The paper states this only for leaders. A follower that escrowed on
  a non-activated arc could lose an asset without compensation.
- **Leader's release rule.** A leader that escrowed nothing (no activated leaving arc) releases its secret
  immediately (proof of Lemma 4). Otherwise it releases it iff all its entering arcs carry assets (proof of
  Lemma 3).
- **A leader deposits its redemption premiums only if all its entering escrow premiums arrived** (proof of
  Lemma 5).
- **Followers whose phase 1 failed still take part in phase 2**, as the text of §7.1 says. This does not hurt
  them.
- **Path checks.** Redemption-premium paths must be simple paths from the depositor to the leader. Hashkey paths
  are paths in the sense of [Herlihy 2018]: all vertices but the last distinct.
  - The §7 definition of "path" admits cycles. If contracts accepted a cycle `(i, x, i)` as a premium path, a
    deviating leader `i` could put a premium on `(v, i)` that activates it. The conforming `v` cannot extend that
    path, so it deposits nothing on its own entering arcs, and they stay inactive. If an entering asset of `v` is
    then missing, `v` pays the escrow premium `E(v, i)` and collects nothing. (Argued here, not formalized.)
    This would falsify the escrow part of Lemma 3 for a `v` that escrowed nothing; Lemma 6 is unaffected, since
    Definition 1 only protects escrowed assets. We do not count it as an error of the paper: Equation (1) does not
    terminate on such a path (`v ∥ (i, x, i)` is neither a path nor a cycle), so the contract could not even
    compute the premium, and the paper's own definition requires distinct vertices.
  - For keys, the analogous problem with simple-paths-and-cycles was found by the model checker of the companion
    `Papers/PODC2018/AtomicCrossChainSwaps`.
- **Arc orientation.** §7 defines a path by arcs `(uᵢ₊₁, uᵢ)`. Figure 3b and all later uses need `(uᵢ, uᵢ₊₁)`.
  We follow the figure (typo).
- **One redemption premium per (key, arc).** The contract keeps the first one. The contract computes premium
  amounts from the path, so a deviator cannot under-deposit.
- **Hashkeys may be presented on an arc whose asset was never escrowed**, so that redemption premiums can be
  refunded.
- **§5.2 swap phase.** Compliant Alice redeems Bob's principal whenever he escrows it, even if her own escrow did
  not happen. Compliant Bob escrows only after both premiums are in and Alice escrowed. Under the alternative
  reading Alice can lose `pa + pb` (`TwoParty.alt_reading_alice_loses`).
- **§9 timing.** A key with path `q` is accepted until `1 + |q|`, counted from the start of the declaration
  phase. Counted from time 0, Alice's key `(A)` would expire at the end of the bidding phase. The winner rule is a
  parameter (ties are unspecified). If there is no winner, a conforming Alice forfeits her `2p`
  (`Auction.no_winner_alice_pays`).
- **§6 indexing.** The closed form `(rA + B)/Pʳ`, `A/Pʳ` holds with `r` counting the main swap's premium round
  (`B⁽¹⁾ = (A+B)/P`). The "$4, 3 rounds, $1,000,000" example matches `A = B = 10⁶`, `P = 100`.

## Modelling choices

- Lock-step synchrony: every conforming reaction lands exactly one `Δ` after its trigger. The paper says
  "at most `Δ`".
- Executions are records of first-occurrence times plus axioms, not a step-by-step state machine. Contract rules
  and unforgeability constrain all parties; conforming parties satisfy equations that define their actions.
  Deviators are otherwise unconstrained, so the safety theorems quantify over a superset of the real executions.
  Front-running is allowed: a signature can be used at the time it is submitted.
- Premiums are natural-number multiples of a single `p`, the paper's "assume for simplicity that each asset has
  the same premium `p`". Payoffs are in `ℤ`.
- Digraphs have no self-loops.
- Base-protocol safety (a conforming party that loses an outgoing asset receives all incoming ones) is not
  re-verified. The paper cites [Herlihy 2018], and the companion formalization shows that Theorem 4.9 there needs
  a repair (a deadline guard on secret release). In our model the leader's release time is always within its
  key's deadline (`rel_le`).

## Proof gaps in the paper

- The proofs of Lemmas 2–6 rely on unstated facts, which we prove.
  - The first premium (`not_mem_fp`) and the first key (`ky_fwd`) a conforming party observes do not contain it.
    This is the unforgeability argument.
  - An activated leaving arc forces all entering arcs to be activated (`act_in`). The leader case needs
    unforgeability of the leader's own premium.
  - The forwarding deadlines line up: `B + |v ∥ q| = B + |q| + 1`.
- Lemma 5's leader case ("its outgoing escrow premiums are refunded eventually") needs unforgeability: nobody can
  deposit the leader's redemption premium on its leaving arcs.
