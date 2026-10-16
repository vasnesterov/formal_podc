# Differences between the formalization and the paper

Paper: Lenzen, Loss, Shi, Wagner. *Byzantine Consensus in the Partially Authenticated Setting.* PODC 2026
(proceedings version, pp. 282–292; the full version ePrint 2026/470 was not used — it is not on arXiv). Numbering
follows the proceedings version.

## Errors and imprecisions in the paper

1. **Theorem 4.1 omits the hypothesis "the sender is unregistered" (imprecise statement; intended meaning clear
   from the surrounding text).** As printed ("Assume there exist s registered parties ... no Byzantine Broadcast
   protocol if t ≥ max{⌈s/2⌉, ⌈n/3⌉}") it contradicts the paper's own Theorems 3.13/3.14: with `n = s = 3`,
   sender registered and `t = 2 = max{⌈3/2⌉, ⌈3/3⌉}`, broadcast is solvable. Lean:
   `theorem41_false_registered_sender` (via `theorem314_solvable`). We prove Theorem 4.1 with `snd ∉ Reg`
   (`theorem41`).
2. **Theorem 4.1 is false for `n = 2` and Corollary 4.2 is false for `n = 1` (false only in a degenerate case).**
   For `n = 2` broadcast is solvable against any number of Byzantine parties (the sender sends its value; the
   other party outputs what it receives), but `max{⌈s/2⌉, ⌈2/3⌉} = 1 ≤ t = 1`. For `n = 1` agreement is trivial.
   Lean: `bb_solvable_card_two`, `theorem41_false_card_two`, `ba_solvable_card_one`, `corollary42_false_card_one`.
   We prove Theorem 4.1 for `n ≥ 3` and Corollary 4.2 for `n ≥ 2` (`theorem41`, `corollary42`). The same caveat
   applies to the "if and only if" of the abstract for broadcast with an unregistered sender.
3. **Figure 1, Phase 2 is ambiguous; under the "else-if" reading Lemma 3.10 is false (under-specified
   definition).** For an unregistered party receiving a valid Extension the figure has two bullets: "if `v = 0`,
   set `v = 1` and send Echo1" and "if `v = 1` and `g = 0`, set `g = 1` and send Echo1". If they are exclusive, a
   party with `(v, g) = (0, 0)` ends with `(1, 0)`. Run (`n = 4`, `Reg = {0 (sender), 1}`, Byzantine `{0, 3}`):
   in super round 1, party 3 sends party 2 an Echo2 with the chain `[0]`; party 2 sets `g = 0` and sends Echo3; the
   honest registered party 1 accepts `[0]` and in super round 2 extends it; party 2 sets `v = 1` but keeps `g = 0`.
   So an honest registered party exists while an honest party outputs grade 0, contradicting Lemma 3.10
   (`Exclusive.lemma310_fails_exclusive`, run `Exclusive.exclusive_run`). Theorem 3.13 then fails too: with the
   black box "AND of the exchanged values" among `N = {2, 3}` (a valid BA when nobody in `N` is Byzantine,
   `andBA_BA`) and `t = 2 < s + ⌈(n−s)/3⌉ = 3`, Byzantine party 3 sends `0`, party 2 (grade 0) outputs 0 and the
   honest registered party 1 outputs 1 (`Exclusive.theorem313_fails_exclusive`, `exclusive_bc_run`). The proof of
   Lemma 3.10 ("sets `v_j = 1` and it must have `g_j = 1` in phase 2") uses the
   sequential reading ("set `v = 1`, then, since `v = 1` and `g = 0`, set `g = 1`"), which we formalize; with it
   all lemmas hold. Lean: `Exclusive.lean` (see README for the exact statement).
4. **Proof gaps with true statements (Section 3).**
   - Lemma 3.3: "each party `P_j` with `v_j = 0` sets `v_j = 1` in phase 2 of super round `k+1`" needs the
     extended chain to be valid *for `P_j`*, i.e. `P_j` not on it. If `P_j` is registered and on the chain, it
     signed, hence had accepted, hence `v_j = 1` already — an unforgeability argument the paper skips. We prove
     a general signature-origin lemma (`emit_origin`, `signed_v`, `signed_sender`): a token of an honest
     registered party `i` seen by an honest party is `c ++ [i]` for the chain `c` that `i` accepted.
   - Lemma 3.4 and Lemma 3.7 (Case 2) state that an unregistered party receiving an Echo2 "sets `v_i = 1`"; by
     Figure 1 it only sets `g_i = 0` (keeping `v_i = 0`). The contradiction still follows, via the grade (it can
     only return to `1` together with `v = 1`); our proofs do this.
   - Lemma 3.7 Case 2's restriction to super rounds `k < s` is unnecessary; the argument works for all `k ≤ s`.
5. **Inconsistent statements of the small-`N` result (typo-level).** Section 3 says that for `n − s < 3` one can
   tolerate `t ≤ s + 1`; Theorem 3.14 says "any number of corruptions"; Lemma 6.1 assumes `t ≤ n − 2`; the
   overview mentions "`t ∈ {s+1, s+2}`". We prove the strongest version: for `n − s ≤ 2`, Π_BC with the OR exchange
   among `N` (Figure 4) solves broadcast against **every** Byzantine set (`theorem314`).

6. **Theorem 5.1 (correct; minor remarks).** Π_auth must have a known round bound `R` (registered parties must know
   when to send, unregistered parties when to decide) — implicit for "deterministic" in the paper; we make it a
   hypothesis (`BoundedAuthBA`). The signatures in the dissemination step and the tie-breaking rule are never
   needed. The result is stronger than stated: only Byzantine *registered* parties count, `2|B ∩ S| < s` suffices
   (`theorem51_unreg`), if unregistered parties count only messages from registered senders.

## Modelling choices

- **Model.** CSLib's synchronous lock-step model `Cslib.Byzantine.LockStep` on the complete graph, deterministic
  history-based protocols, static Byzantine set, reliable channels, rushing adversary that eavesdrops. The paper's
  adversary is adaptive; for deterministic protocols a static adversary choosing the final corrupted set in
  hindsight is equivalent (it can simulate the honest behaviour before corruption, and it holds the keys of the
  corrupted parties). Lower bounds against a static adversary are stronger (as the paper notes).
- **Signatures.** Ideal signatures are CSLib's abstract tokens; the partially authenticated setting is the
  restriction that every token in every message has a registered signer (`RegisteredSigners`, `SolvablePA`).
  This matches the paper's `F_sign^{S,N}` interface (sign/verify only). Unforgeability for honest parties is
  `Protocol.Unforging`, for the adversary `Scenario.AuthValid`.
- **Lower bounds** quantify over all deterministic protocols (any message and token types). Randomized protocols
  are not covered. The paper does not restrict Theorem 4.1 / Corollary 4.2 to deterministic protocols (Section 2
  leaves the protocol class open), so our `theorem41`/`corollary42` prove the deterministic case only; Theorem 4.3
  (randomized, delayed public state) is not formalized.
- **Π_GC encoding.** A chain is the list of its signers (sender first); the tokens of a message are the nonempty
  prefixes of its chain whose last signer is registered (signature of that signer on the preceding chain). The
  binary protocol signs only value 1 (chains are implicitly on value 1, as in the paper's binary protocol). A
  message is `(phase, chain)`; Echo3 is sent only to registered parties. When several valid chains arrive, an
  arbitrary one (classical choice) is accepted/echoed — the paper does not specify; all proofs hold for any
  choice.
- **Rounds.** Super round `k` = rounds `4(k−1) … 4k−1`; decisions at round `4s` (Lemma 3.8).
- **Π_BC composition.** Rounds `≥ 4s` run the black-box BA `ba` among `N = Regᶜ` (CSLib `Solves` on the
  subtype, complete graph). Parties with grade 1 and registered parties decide at round `4s`, grade-0 parties
  decide what `ba` decides; nobody stops sending. We do not need `ba` to have a fixed round count. The black box is
  required to solve BA against every Byzantine set `B ⊆ N` with `3|B| < |N|` (the paper: "tolerates up to
  `⌈(n−s)/3⌉ − 1` Byzantine parties"), which is the same.
- **Theorem 3.13's bound** is written `t < s + ⌈(n−s)/3⌉` (`t < Reg.ncard + (n − Reg.ncard + 2)/3`), equivalent to
  the paper's `t ≤ s + ⌈(n−s)/3⌉ − 1` (and to `3t < n + 2s`), avoiding truncated subtraction.
- **Theorem 4.1/Cor. 4.2 bounds** are written `max ((s+1)/2) ((n+2)/3) ≤ t`, i.e. `t ≥ max{⌈s/2⌉, ⌈n/3⌉}`, for any
  value type with two distinct values.
- **Π_SBA** (Theorem 5.1): registered parties run the black box for `R` rounds, send their first decision in
  round `R`; unregistered parties decide at round `R + 1` the majority of values received from registered parties.
- **Theorem 3.14** is proved with the paper's Figure 4 protocol for all `n − s ≤ 2` (including `s ≥ n − 1`, where
  the paper cites Dolev–Strong instead).

## Not formalized

- The multivalued protocol (full version only), Theorem 3.15 (communication complexity).
- Theorem 4.3 (randomized lower bound in the delayed-public-state model) and the shared-coin protocol of
  Section 4.3.
- The black boxes themselves: unauthenticated BA among `n − s` parties for `3t' < n − s` (Theorem 3.13) and
  authenticated BA among `s` parties for `2t < s` (Theorem 5.1). For `n − s ≤ 3` the first black box is discharged
  (`theorem313_small`).
