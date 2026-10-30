# Differences between the formalization and the paper (arXiv 2412.19649 v1)

Verdict rules refer to `.claude/skills/formalize-paper/verdicts.md`.

## Statement-level issues (decide the verdict)

1. **Lemma 5.13, Lemma 5.15 and the correctness of Algorithm 7 are false** (`Rapid.lemma_5_13_false`,
   `Rapid.lemma_5_15_false`, `Rapid.rapid_not_solves`). The counterexample has `k = 4`, `n = 4`, `f = 2`
   (`β = 1/2`) and satisfies the standing assumption `n ≥ k`. It is not degenerate (R2). The fix is not
   local (R3): the leader's index selection (line 8) and/or the unconditional increment (line 23) would
   have to change. The paper's proof reasons with the protocol as written.
   - *R4 / Table 2.* Table 2 restricts Theorem 5.16 to `β ≤ 1/k` (one crash). But Theorem 5.16, §1.4.3
     ("tolerate an arbitrary fraction β < 1 of crashes … improves the time to `O(n + βk)`") and the
     abstract claim it for every `β < 1`, so the explicit claim of more generality is not excused.
   - *R5.* Lemmas 5.13 and 5.15 are numbered lemmas, so they are statements, and they are false (❌).
     Theorem 5.16 is existential ("there is a deterministic protocol"), and we did not refute it; it is
     only unestablished for `f ≥ 2`, which gives ❌, not 🚨.
   - *Robustness.* The pseudocode does not fix the round timing. We use the timing of the paper's
     Remark 1: a message sent in round `r` arrives at the end of round `r`; a peer invoking `view change`
     sends in the next round and is idle at the end of that round only. A Python simulator
     (`ByzantineDownload-work/sim7.py`, not part of the deliverable) also finds index skips under the
     alternative "idle for two rounds" timing (`n = 6`, `k = 4`, `f = 2`). The mechanism there is
     different: a peer whose `F` lacks a crashed peer sends its view change to that crashed peer and
     re-sends one round late. For `f = 1` the simulator found no failure for `k ≤ 4`, `n ≤ 4` (bounded
     search, not a proof).
2. **Remark 2 of §5.2** ("M will work on `i + 1`") contradicts line 8 when the higher index arrives in a
   later round. That is exactly what happens in the counterexample. This is a claim in a remark and
   does not count separately.
   - *Remark 2 as a repair (reviewer check).* One might read Remark 2 as the intended behaviour: a leader
     that receives a higher index in a later round of its view switches to it (querying the bit if
     needed) for its remaining transmissions. Under that reading, the Lean run above is avoided. But the
     same simulator, so modified (Remark-1 timing, one idle round), still finds failures with `n = 6`,
     `k = 4`, `f = 2`: e.g. `lead(1)` crashes in round 2 and its second message reaches only `M3`, and
     `lead(4)` crashes in round 11 and its second message reaches only `M3`. `M3` never suspected
     `lead(1)`, so it sends its view change with the higher index to the crashed `lead(5)`. The leader
     of view 6 never sees that index, works on the lower one, and line 23 lets `M3` skip bit 5. So the
     failure does not depend on the line-8 reading. This is a bounded simulation, not a Lean proof, and
     it is not part of the verdict.

## Proof-level issues (no effect on the verdict beyond 🛠️)

3. **Lemma 3.4, Eq. (8).** "For any `Byz ∈ B`, `p(R̂(Byz)) > (1 − e⁻¹)/2`" is false for some `Byz`; only
   the average over `B` is bounded. The paper then applies the involution `Byz ↦ Byz^inv` to sets
   `Byz^inv_R` that depend on `R`, as if they were fixed sets. Our proof fixes `R` first, uses the
   involution on `{Byz ∈ B : v(R) ∉ Byz}` and the ratio `C(n−1, (n−1)/2) / C(n, (n−1)/2) ≥ 1/2`, and then
   averages (`choose_le_sum_involution`, `choose_le_two_mul`).
4. **Lemma 3.3.** "Under constraints (6) and (7), `q(i)` is maximized when `p_v(i) = 1/n`" is asserted
   without proof. We prove `min_i ∏_v (1 − p_v(i)) ≤ e⁻¹` by pigeonhole (`Σ_i Σ_v p_v(i) ≥ n`) and
   `1 − x ≤ e^{−x}`. The paper's strict `< e⁻¹` becomes `≤`, which suffices.
5. **Lemma 5.2.** The chain argument is replaced by a counting argument. If at some iteration `s` a peer
   knowing `b_I` survives round `s`, everybody alive knows `b_I` afterwards. Otherwise the knowers of
   iterations `0, …, f` crash in distinct rounds, giving `f + 1` faulty peers, or some iteration has no
   knower, and then no live peer ever learns `b_I`. The paper says "all peers"; we prove the statement for
   the peers alive at the end of the view, which is what Lemma 5.4 needs.
6. **Theorem 5.9's query bound.** "Every nonfaulty peer leads at most `n/γk` good views" is imprecise.
   We prove `Q·(k − f) ≤ n + k − 1` for every nonfaulty peer (`theorem_5_9_queries`). With `n ≥ k` and
   `f ≤ βk` this gives `Q ≤ 2n/(γk)` (`theorem_5_9`). The proof counts view numbers whose leader is
   nonfaulty, since such views are never skipped (`roundRobin_count`).

## Modelling choices and minor differences

7. **DR model (crash part).**
   - *Rounds.* The three sub-rounds are encoded as `query`, `ans`, then `send` and `step`. Local
     computation happens at the start of sub-rounds. Messages may be sent to oneself.
   - *Crashes.* A peer crashing in round `c` makes its round-`c` queries and delivers its round-`c`
     messages to an adversarial subset of peers; its state is then frozen and never read. A crash
     pattern with `c = 0` means the peer is dead from the start.
   - *Measures.* Only nonfaulty peers' queries and messages are counted, as in the paper's `Q` and `M`.
     Download "upon termination" is stated as "from time `T` on, `res = X` for every nonfaulty peer".
8. **Algorithm 6.**
   - *Indexing.* `lead(v) = v mod k` with peers `Fin k = {0, …, k−1}`, which fixes the IDs `[1, k]` vs
     `mod k` typo. Indices are 0-based internally.
   - *Messages.* `⟨view v, i, b⟩` is kept. A peer takes the first (lowest sender ID) received message of
     its current view and sets `res[i] ← b` for that message's `i`. The paper says "from at least one
     peer"; all such messages coincide.
   - *Running and stopping.* The leader queries in the query sub-round of the first round of the view. A
     peer with `I ≥ n` stops sending and querying (`while I(M) ≤ n`). `f` is a parameter known to the
     peers, as in the paper.
9. **Algorithm 7, interpretation choices** (`RapidDownload.lean`, module docstring).
   - *Timing.* As in item 1.
   - *Initialisation.* Not specified in the paper: `lead(1)` starts view 1 at time 0 with index 1.
   - *Leader.* The leader receives its own view messages and handles them like any peer. A view change
     to oneself is a message to oneself. The leader queries in the round after it receives the first
     view-change messages, then sends in that round and the next.
   - *Silence.* "Not receiving a message from `lead(view)`" counts any message from `lead(view)`, or any
     view message of a view `≥ view`, as hearing from it.
   - *Finishing.* A peer with `I > n` (0-based `I ≥ n`) no longer suspects, changes view or leads. This
     only affects the run after the bit has been lost: indices only increase, so the lost bit is never
     sent again anyway.
10. **Lower bound (§3).**
    - *Peers and bits.* `n` peers and `n` bits, as in §3; `n ≥ 1` is needed in Lemma 3.3 (for `n = 0` it
      is vacuously false; R2).
    - *Randomness.* Random strings live in finite types with independent private weights. The paper sums
      over random profiles, so it implicitly uses discrete distributions.
    - *Query bound.* `A(n−1, 1)` is "every peer queries at most `n − 1` bits for every random string"
      (worst case, as the paper's proof uses).
    - *Adversary.* Fixed rather than random. Byzantine peers use their own random strings to simulate the
      algorithm on `X^inv`. This is stronger than the paper's random choice of `Byz`.
    - *Broadcast model.* Covered by `theorem_3_6_broadcast`: if honest messages do not depend on the
      recipient, neither do the adversary's.
11. **Not formalized.**
    - Theorem 5.16's time and message bounds, which are moot for `f ≥ 2`, and a proof of Algorithm 7 for
      `f ≤ 1`.
    - Lemmas 5.10–5.12 and 5.14 individually.
    - All randomized Byzantine protocols (§2, §4), the asynchronous crash protocols (§6) and message
      sizes (`O(log n)` bits).
12. **Message complexity of Theorem 5.9.** We bound the messages per nonfaulty peer,
    `≤ (k − 1)(n + f)(f + 1)`, so the total is `≤ k(k − 1)(n + f)(f + 1) = O(k² f n)` for `f ≥ 1`.
    `T = (n + f)(f + 1)` is `O(nf)` only for `f ≥ 1`; for `f = 0` it is `n` (R2).
