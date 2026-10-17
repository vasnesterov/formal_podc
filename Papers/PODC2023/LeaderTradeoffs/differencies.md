# Differences between the formalization and the paper

Kutten, Robinson, Tan, Zhu. *Improved Tradeoffs for Leader Election.* PODC 2023 (arXiv 2301.08235v4).

Classification: **F** false statement, **FD** false only in a degenerate case, **G** proof gap with
true (repaired) statement, **D** under-specified / defective definition, **T** typo or slip,
**M** modelling choice.

## Errors in the paper

1. **F — Theorem 3.8, the `+ 1`.** The paper claims `T(n) > (log₂ n − 1)/(log₂ f(n) + 1) + 1`.
   This fails for every power of two `n ≥ 2` with `f(n) = n` (increasing, `> 1`) and an ID universe of
   the required size `2n log₂ n + n`: the one-round broadcast algorithm (every node sends its ID to all,
   the maximum wins, decisions are irrevocable and nodes are silent afterwards: `broadcast_terminatesBy`)
   has `T = 1` and sends `n(n − 1) ≤ n f(n)` messages, while the claimed bound
   exceeds `1` (`theorem_3_8_as_stated_false`, `Counterexamples.lean`). Only this one-round regime
   (`f ≥ n − 1`) is refuted; for `T ≥ 2` the stated bound is unproved, not refuted.
   Cause: Lemma 3.9 bounds the components of `G_r`, which contains only the messages of rounds `< r`;
   the proof applies it with `r = T`, so the messages of the last round are ignored (the induction step
   of Lemma 3.9 also builds `G_{r+1}` from the messages "sent during round `r + 1`", which is the same
   index slip). Applying the lemma after round `T` gives
   `T > (log₂ n − 1)/(⌈log₂ f⌉ + 1)`, in fact `log₂ n ≤ (⌈log₂ f⌉ + 1)·T`
   (`theorem_3_8_corrected`, `tradeoff_lower_bound`).
2. **F/G — the "consequently" part of Theorem 3.8** (`k`-round algorithms need
   `Ω((n/2)^{1+1/(k−1)})` messages) is derived from the false bound. With the corrected bound one gets
   `Ω(n^{1+1/k})` (`rounds_messages_tradeoff`: if `(c + 1)T < log₂ n`, `c ≥ 1`, then some execution sends
   more than `n·2^c` messages). For `k = 1` the paper's formula is undefined; whether the paper's
   exponent `1 + 1/(k − 1)` is true for `k ≥ 2` (e.g. `Ω(n²)` for 2-round algorithms) is neither proved
   by the paper nor decided here. The comparison with Afek–Gafni (`Ω(k n^{1+1/(2k)})`) remains a
   polynomial improvement for constant `k`.
3. **G — ceiling in Theorem 3.8.** The statement uses `log₂ f(n)`, the proof uses
   `σ_r = (⌈log₂ f(n)⌉ + 1)(r − 1)`, and the final step `2^{σ_T} ≤ 2^{(log₂ f(n) + 1)(T − 1)}` goes in the
   wrong direction when `f` is not a power of two. We prove the version with `⌈log₂ f⌉`; the version
   without ceiling is not established (the two differ by less than a factor 2 in `f`).
4. **D — Definition 3.5 / Lemma 3.6 / Corollary 3.7.** "`X` forms terminating components if there is a
   round `r` such that for **every** prefix `E ∈ Exec_r(X)` all nodes of `X` have terminated" is vacuously
   true when `Exec_r(X)` is empty, which is the typical case (e.g. when a node sends on more than `|X| − 1`
   ports). For the broadcast algorithm every set of fewer than `n` IDs is "terminating" in this sense,
   so Lemma 3.6 (at most `n/2^ℓ` disjoint terminating `2^ℓ`-sets) and Corollary 3.7 are false for the
   literal definition (`terminatingLiteral_broadcast`, `lemma_3_6_literal_false`, with an algorithm that
   terminates with irrevocable outputs in one round: `n = 2`, `ℓ = 0`,
   three disjoint singletons). The proof of Lemma 3.6 uses the existential reading ("there exists a
   partial port mapping `p_i` such that the nodes of `X_i` only send messages inside `X_i`"); with it
   (`Isolable`) Lemma 3.6 and Corollary 3.7 hold (`not_disjoint_isolable`,
   `exists_universe_no_isolable[_pow]`), and this is also what the uses in Theorems 3.8 and 3.11 need.
5. **G — ID universe in Theorem 3.11.** Lemma 3.14 assumes `n T'^{log₂ n − 1} + n log₂ n` IDs for the
   single-send algorithm (time `T' = nT` after Lemma 3.12), i.e. `n^{log₂ n} T^{log₂ n − 1} + n log₂ n`;
   Theorem 3.11 (and Lemma 3.13) state the bound without the `n log₂ n` IDs removed by Corollary 3.7.
   We prove Theorem 3.11 with `n log₂ n + n^{log₂ n} T^{log₂ n − 1}` IDs (`theorem_3_11`) and Lemma 3.13
   with `n log₂ n + n T^{log₂ n − 1}` (`single_send_lower_bound`).
6. **G — Lemma 3.14, property (a).** When merging `C` and `C'` the proof connects the ports opened by
   `C` through "any one-to-one mapping `g`" into `C'` and those opened by `C'` through an independent
   `h` into `C`; a node can then get two new links (one it opened, one it received), leaving capacity
   `2^i − 2` instead of the claimed `|D|/2 − 1 = 2^i − 1`. Fixed by linking along a perfect matching
   `β : C → C'` (a node `u` that opens a port and its partner `β(u)` share the same link) (`merge`).
7. **G — Lemma 3.14, property (c).** `|U_i'| ≥ |U_i|/T` counts sets, but the property needed is the
   number of *pairwise disjoint* sets; the pigeonhole must be applied to a disjoint subfamily. We keep
   an indexed family of pairwise disjoint sets throughout (`Level`, `level_step`).
8. **G — Lemma 3.14, quantifiers.** "For every set `I ∈ U_i`, every execution prefix `E ∈ Exec_{r_i}(I)`,
   there exists a partial port mapping `p` such that …" is not what the construction provides (the
   round `r_I` depends on the chosen execution). We fix one isolated execution per set
   (the one built by the adversary); this suffices for Lemma 3.13.
9. **G — absorbing phase (Lemma 3.14).** The proof invokes Lemma 3.3 to connect the first `|C|/2 − 1`
   newly opened ports inside `C` but does not say how; with several nodes opening ports in the same
   round and hubs receiving many links, capacity must be tracked per node. We link each opener to one
   not-yet-linked node of its set and track `capacity ≥ c − (messages absorbed so far)` (`absorb_round`,
   `absorb`).

10a. **T — Theorem 3.10.** "There remains only a single survivor at the end of the `(k − 1)`-th iteration":
    the analysis gives at most `n^{1/(k−1)}` survivors after the last two-round iteration, and the final
    broadcast round elects the maximum among them (its `n^{1/(k−1)}·(n − 1)` messages fit the claimed bound).
    The referee counts `⌈n^{i/(k−1)}⌉` may exceed `n − 1` for small `n`; the formal algorithm uses
    `min(d_i, n − 1)`. Proved: correctness for any `K` and any referee counts, the generic bound
    `Σ_t 2 s_t d_{t+1} + s_K (n−1)` (`Referees.msgs_le`), and `≤ 4(ℓ+1) n^{1+2/(ℓ+1)}` for `ℓ = 2K+1`
    (`Referees.theorem_3_10`).
10b. **D — Algorithm 1 (Theorem 3.15).** The pseudocode does not say that a node stops after selecting a
    leader (needed: otherwise later blocks broadcast too, the message bound fails and the selection is
    overwritten), and for `n = 1` "selects when it receives messages" never fires (the formal algorithm also
    selects when it sent). The hypothesis `d ≤ n` is unnecessary. Proved: explicit leader election of the
    minimum ID within `⌈n/d⌉` rounds, at most `(n − 1)·d·g ≤ n·d·g` messages (`SmallIds.*`).

## Strengthenings / deviations in the formal statements

10. **M — correctness notion.** Lower bounds assume only `ElectsBy A U T`: in every execution with IDs
    from `U` and every port mapping, exactly one node outputs "leader" after round `T`. This is weaker
    than the paper's (implicit) leader election with termination by round `T`, so the lower bounds
    are stronger. Message bounds (`MsgBound`) count only messages sent in rounds `1..T`.
11. **M — the bound in Theorem 3.11 is explicit:** at least `(n/2) log₂ n` messages (the paper's proof
    gives `(n/2)(log₂ n − 1)`; we also count the first merge level: two singletons must exchange a
    message). Requires `n = 2^k`, `k ≥ 2` (the paper: `n` a sufficiently large power of two).
12. **M — Theorem 3.8** is proved for every power of two `n` (no "sufficiently large"), every real
    `f > 1` (no monotonicity in `n` needed: `n` is fixed), with the paper's universe size
    `2n log₂ n + n`; the core form `tradeoff_lower_bound` needs only `(T + 2)·n` IDs.
13. **M — Lemma 3.12** simulates every round by `n` sub-rounds (sub-round `i < n − 1` sends A's message
    for port `i`, the last sub-round is idle); time exactly `n·T`, message counts equal for every port
    map (`msgs_simulate`).
14. **M — Lemma 3.6** is proved for any block size `s` with `n = s·N`, `N ≥ 2`; the proof is a counting
    argument (`Σ_{a≠j} c_a = 1` for all `j` is impossible for `N ≥ 2`) instead of the "WLOG `a ∈ X_1`"
    case analysis.
15. **M — Corollary 3.7** removes at most `n` IDs per block size (`exists_universe_no_isolable`), as in the
    paper; Theorem 3.8 only needs the single size `2^{σ_T}`.

## Not formalized

- Theorem 3.16 (Las Vegas lower bound, randomized), Section 4 (adversarial wake-up: Theorems 4.1, 4.2),
  Section 5 (asynchronous algorithms).
