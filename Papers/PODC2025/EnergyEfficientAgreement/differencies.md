# Differences between the formalization and the paper

Paper: Mirault–Robinson, *Brief Announcement: Towards Energy-Efficient Distributed Agreement*, PODC 2025 (BA).
Proofs omitted in the BA are taken from its full version arXiv:2506.12282v1 ("full"), which the BA cites as [12].
Numbering: BA Algorithm 1 = full Algorithm 2; BA Lemmas 1–4 = full Lemmas 2–5; BA Theorem 2 = full Theorem 6;
`JoinCommittees` = full Algorithm 1; binary algorithm = full Algorithm 3.

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Theorem 2 (binary consensus) — the algorithm is incorrect; the claim is unestablished. ❌ (R1, R5).**
   - *What fails.* The full version's Algorithm 3 with its `JoinCommittees(f, ⌈√n⌉)` and `T₀ = ⌈(f+1)/√n⌉` violates
     agreement for `n = 5, f = 3`, `n = 7, f = 4` and `n = 9, f = 7` (Lean: `algorithm3_violates_agreement`,
     `_7_4`, `_9_7`).
   - *Not degenerate (R2).* `n = 5`, `f = 3` leaves two non-faulty players, and `n = 7` leaves three. A simulation
     (`scripts/family.py`) gives a disagreeing execution for every `n = s²`, `f = n − 2`, `3 ≤ s ≤ 12`.
   - *The BA sketch fails too.* It leaves the committees unspecified ("analogously to the multi value consensus
     algorithm"). For `n = 5`, `f = 3` the sketch fails for **all** 1000 assignments of 3 committees of size 3
     (`scripts/allcomm.py ba`). For the full version's exact rules, 970 of the 1000 assignments fail
     (`scripts/allcomm.py v1`; the 30 exceptions have `C₁ = C₂`).
   - *Why the Lean executions also cover the sketch.* The sketch differs from Algorithm 3 in two places. Input-1
     players send to `C_1..C_T` (Algorithm 3: `C_1..C_{T+1}`), and the sketch never re-activates them. The Lean
     executions use neither difference, since the only input-1 player crashes in round 1.
   - *Why ❌ and not 🚨.* Theorem 2 is phrased existentially ("There is a deterministic algorithm …"), and the
     abstract says "we show that `O(⌈f/√n⌉)` rounds are possible". The paper's algorithm is wrong, but the
     existential claim is not refuted, only unestablished (R5). The authors' later OPODIS 2025 paper (arXiv v2,
     with Meir and Peleg) describes this attack and gives a different algorithm for the same bounds. We did not
     check it, so the claim stays unestablished here. *Borderline:* a reader may see the BA's binary algorithm
     as the headline itself ("our binary consensus algorithm operates as follows"). Under that reading the
     verdict would be 🚨.
   - *Full-version lemmas.* Lemma 11 ("either `|P_{f+1}| ≥ f + 1` or the algorithm reaches agreement on 0") is
     false: in the `n = 5` execution `P₄ = {p₂, p₃, p₄}`, and the decisions differ. Its proof assumes that a
     1-valued message is sent and delivered to a new player in every round from `t` on. In the execution, the
     round-3 message goes to `C₃`, whose other members have crashed, and the crashed senders of rounds 1–2
     deliver to only one player each. Lemma 9 ("no player receives `1` in two distinct rounds while `|P| ≤ f`") also
     fails if a relay's message to its own committee counts: `p₄` receives `1` in rounds 2 and 3. Section 4.1 of the
     full version assumes that a member of `C_i` is in none of `C_{i+1}, …, C_{i+⌈√n⌉+1}`. Algorithm 1
     (`JoinCommittees`) does not give this; for `n = 9`, `C₄ = C₁`. No assignment can give it once
     `f > ⌈√n⌉`, or `f = ⌈√n⌉` with `n` not a perfect square (e.g. `n = 5`, `f = 3`): the property makes
     `min(f, ⌈√n⌉ + 2)` consecutive committees of size `⌈√n⌉` pairwise disjoint, which needs more than `n`
     players since `⌈√n⌉² ≥ n`.
2. **Lemma 2 is false as stated — ⚠️ (R3).** The hypothesis "`p` is alive in round `i`" means, by the paper's own
   definition, not crashed in rounds `1, …, i − 1`. So `p` may crash in round `i` and its message to `C_i` may be
   lost (`lemma_2_as_stated_false`: `n = 2`, `f = 1`). The proof uses "`p` successfully sends its message to all
   destinations", so the intended hypothesis is recoverable and the fix is local: `p` does not crash in round `i`.
   Lemma 3's proof applies Lemma 2 only in this form. Proved as `lemma_2`, in the stronger form "every decider
   decides `≥ v`".
3. **Lemma 3** carries a hypothesis `m ≥ δ` that is not needed. `lemma_3` is proved without it. Here `m` is the
   maximum over the members of `C_i` that have not crashed by the end of round `i` (the strongest reading).
   The proof is direct propagation along non-faulty committee members (`mv_le_correct`) and does not go
   through Lemma 2.

## Proof-level issues (statements true)

4. **Lemma 4 (agreement) — proof repaired 🛠️.**
   - The case where the first clean round is `t = f + 1` is missing. The proof covers only `t = 1` and
     `1 < t < f + 1`. Repair: every decider receives all alive `C_f` members, and Lemma 3 bounds its own value.
   - "Since `p` does not crash" is unjustified. `p` is an arbitrary alive member of `C_t` holding `δ` and may crash
     later. Repair: after a clean round `t ≤ f`, all alive members of `C_t` hold the same value (`mv_clean_le`, via
     Lemma 3 at round `t − 1`), so the non-faulty member of `C_t` holds it and carries it to round `f + 1`.
   - Case `t = 1` ("it follows from Lemma 2 that no player has an input greater than `δ`") is fine for the
     corrected Lemma 2 because nobody crashes in round 1.
   - Our proof (`lemma_4`) does not use `δ`. It shows directly that every decider decides the same value: the
     common value after the clean round, or the maximum over `C_f`.
5. **Energy bound of Theorem 1.** The BA gives only the one-line argument. We prove the explicit bound
   `2 + 2·#{i ≤ f : p ∈ C_i} ≤ 2 + 2⌈f(f+1)/n⌉` (`mv_awakeCount_le`, `card_filter_mem_joinCommittees_le`).
6. **Message bound of Theorem 1.** We prove `(f+1)·k² + 2nk` for committees of size `≤ k`, which gives
   `(f+1)³ + 2n(f+1)` for `k = f + 1` (`mv_msgCount_le`). The paper's count is
   `n(f+1) + (f−1)(f+1)² + (f+1)n`; ours bounds rounds `1` and `f + 1` by `(f+1)²` more each. Both are
   `O(f³ + nf)`.

## Modelling choices

7. **Sleeping model.**
   - Awake/asleep is a function of the round number and the state at the start of the round, i.e. an alarm set at
     the last awake round. An asleep player does not change state.
   - A message is delivered iff its sender has not crashed before the round, is awake, and (in its crashing round)
     the recipient is in the adversary's `reach` set, and the recipient is awake. This is exactly the BA's "only an
     arbitrary subset of messages sent by `p` are guaranteed to be delivered".
   - Self-messages are allowed. For Algorithm 1 they make no difference. In Algorithm 3 a relay's message to its own
     committee reaches itself, which changes nothing because `Y` is already 1.
8. **Deciders.** Every player that has not crashed by the end of round `f + 1` decides its `Y`. Agreement and
   validity are proved for all of them, which is slightly stronger than for "non-faulty" players. Termination at
   round `f + 1` holds by construction.
9. **Values.** Multi-value inputs come from an arbitrary linear order (the paper uses integers, "polynomial in
   `n`"). This is a generalization. Message sizes (`O(log |Δ|)` bits, constant for binary) are not formalized:
   each message carries a single value or a single bit.
10. **`f ≥ 1`** is assumed for Algorithm 1 (R2: with `f = 0` the pseudo-code refers to `C_0`). `f < n` is needed
    for the committees of size `f + 1` (from `JoinCommittees(f, f+1)`, Algorithm 1 of the full version). The
    correctness lemmas (`lemma_2`, `lemma_3`, `lemma_4`) hold for **any** committees with more than `f`
    members.
11. **`JoinCommittees`** is formalized as in the full version. Slot `i ∈ [1, ab]` goes to player `i mod n` and
    committee `⌈i/b⌉`. The BA only requires "at most `⌈f(f+1)/n⌉` committees per player", which we prove.
12. **Ceilings.** In `algorithm3`, `⌈√n⌉` and `⌈(f+1)/√n⌉` are real ceilings (`Nat.ceil`), evaluated with
    `ceil_sqrt_eq` and `ceil_div_sqrt_eq`.
13. **Algorithm 3 details.** In round `h ∈ [2, f]` an active player decrements `T` (line 12) and an activation
    in the same round resets it to `T₀` (line 17). This follows the order of the pseudo-code. In round 1 a player
    with `X = 1` sets `T ← T₀` (line 5) even if it is not activated. In round `f + 1` a player with
    `X = 1` decides 1 (line 21). The counterexamples do not depend on these choices: the input-1 player crashes in
    round 1, and every relay is activated exactly once.
