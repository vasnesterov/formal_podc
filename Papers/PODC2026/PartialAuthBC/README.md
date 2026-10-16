# Byzantine Consensus in the Partially Authenticated Setting — PODC 2026

Christoph Lenzen, Julian Loss, Kecheng Shi, Benedikt Wagner. *Byzantine Consensus in the Partially Authenticated
Setting.* PODC 2026. DOI [10.1145/3796701.3815929](https://doi.org/10.1145/3796701.3815929). Formalized version:
the proceedings version (pp. 282–292); numbering follows it. The full version (ePrint 2026/470) was not used.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main positive result holds: the gradecast Π_GC works against any number of
corruptions and has the special grade-1 property (Theorem 3.9, Lemma 3.10). The broadcast Π_BC for a registered
sender tolerates `t ≤ s + ⌈(n−s)/3⌉ − 1` given the black-box BA among the unregistered parties (Theorem 3.13), and
Theorem 3.14 holds. All of this needs the right reading of an ambiguous step in Figure 1. The lower bound
(Theorem 4.1, Corollary 4.2) holds once two missing hypotheses are added: an unregistered sender, and `n ≥ 3` for
broadcast (`n ≥ 2` for agreement). Theorem 5.1 holds.

## Mistakes in the paper

- **Theorem 4.1 omits "the sender is unregistered" (imprecise statement; true with it).** As printed, it
  says broadcast is impossible whenever `t ≥ max{⌈s/2⌉, ⌈n/3⌉}`. This contradicts the paper's own Theorem 3.14:
  with `n = s = 3`, a registered sender and `t = 2`, broadcast is solvable. The surrounding text makes clear that an
  unregistered sender is meant. We prove the theorem with this hypothesis. (`theorem41_false_registered_sender`,
  `theorem41`)
- **Theorem 4.1 fails for `n = 2`, Corollary 4.2 for `n = 1` (false only in degenerate cases).**
  - For `n = 2`, broadcast is solvable against any number of faults: the sender sends its value and the other
    party outputs what it receives. Yet `max{⌈s/2⌉, ⌈2/3⌉} = 1 ≤ t = 1`.
  - For `n = 1`, agreement is trivial.
  - The cover proof needs three nonempty groups for broadcast (two for agreement). We prove Theorem 4.1 for
    `n ≥ 3` and Corollary 4.2 for `n ≥ 2`.
  - The "if and only if" of the abstract inherits the `n = 2` exception for broadcast.

  (`theorem41_false_card_two`, `corollary42_false_card_one`, `theorem41`, `corollary42`)
- **Figure 1, Phase 2 is ambiguous. Under the else-if reading, Lemma 3.10 and Theorem 3.13 are false
  (under-specified definition).**
  - **The ambiguity.** An unregistered party that receives a valid Extension has two rules: "if `v = 0`, set
    `v = 1` and echo" and "if `v = 1` and `g = 0`, set `g = 1` and echo".
  - **The else-if reading fails.** If the two rules exclude each other, a party in state `(0, 0)` ends in
    `(1, 0)`. Example with `n = 4`, `S = {0 = sender, 1}`, and Byzantine parties `{0, 3}`:
    - in super round 1, party 3 sends party 2 an Echo2 with the 1-chain `[0]`;
    - party 2 sets `g = 0` and sends Echo3, so the honest registered party 1 accepts `[0]`;
    - in super round 2, party 1 extends the chain, and party 2 sets `v = 1` but keeps `g = 0`.

    So party 2 outputs grade 0 although an honest registered party exists.
  - **Theorem 3.13 breaks too.** Take as Π_unau among `N = {2, 3}` the protocol "AND of the exchanged values",
    which is a valid BA when nobody in `N` is faulty. Party 3 sends 0, so party 2 outputs 0 while party 1 outputs
    1, with `t = 2 ≤ s + ⌈(n−s)/3⌉ − 1`.
  - **The fix.** The proof of Lemma 3.10 uses the sequential reading: "set `v = 1`; now `v = 1` and `g = 0`, so
    set `g = 1`". After a valid Extension the party is in `(1, 1)`. We formalize this reading, and all lemmas hold.

  (`Exclusive.lemma310_fails_exclusive`, `Exclusive.theorem313_fails_exclusive`)
- **Proof gaps in Section 3 (statements true).**
  - **Lemma 3.3.** "Every `P_j` with `v_j = 0` accepts the extended chain" requires `P_j` not to be on the chain.
    If it is on the chain, it signed it, so it already has `v_j = 1`. This unforgeability step is skipped. We
    prove a general origin lemma: a signature of an honest registered `i` seen by an honest party is `c ++ [i]`,
    for the chain `c` that `i` accepted. (`emit_origin`, `signed_v`)
  - **Lemmas 3.4 and 3.7.** Their proofs say that an unregistered party receiving an Echo2 "sets `v = 1`"; it only
    sets `g = 0`. The contradiction still follows through the grade.
- **Minor.**
  - Three different versions of the small-`N` result appear: `t ≤ s + 1`, "any number of corruptions"
    (Theorem 3.14), and `t ≤ n − 2` (Lemma 6.1). We prove the strongest one: for `n − s ≤ 2`, every Byzantine set.
  - Theorem 5.1 implicitly needs Π_auth to have a known round bound. Its statement is stronger than claimed: only
    Byzantine *registered* parties count (`theorem51_unreg`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Base model.** CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`):
  - deterministic history-based protocols on the complete graph;
  - reliable channels;
  - a static, rushing, eavesdropping adversary.

  For deterministic protocols, the paper's adaptive adversary is equivalent. Lower bounds against a static
  adversary are stronger.
- **Signatures.** Ideal signatures are CSLib's abstract tokens (unforgeability via `Protocol.Unforging` and
  `Scenario.AuthValid`). *Partially authenticated* means that every token has a registered signer
  (`RegisteredSigners`, `SolvablePA` in `Model.lean`). This matches `F_sign^{S,N}`.
- **Π_GC (binary).** A chain is the list of its signers. The signature tokens are the prefixes of the chain that
  end in a registered signer. Super round `k` is rounds `4(k−1)..4k−1`, and the output is at round `4s`.
- **Π_BC.** Π_GC is followed by a black-box unauthenticated BA `ba` on the subtype `N = Regᶜ`. The black box must
  tolerate every `B ⊆ N` with `3|B| < |N|`. No fixed round count is needed.
- **Lower bounds** quantify over all deterministic protocols, message types and token types (the paper does not
  restrict Theorem 4.1 to deterministic protocols; randomized ones are not covered).

**Main results in Lean** (namespace `PartialAuthBC`).

| Paper | Lean | File |
|---|---|---|
| Thm 3.9 (Π_GC is gradecast, any number of faults) | `theorem39`, `gradecast_solvablePA`, `gc_unforging` | `Gradecast.lean` |
| Lemmas 3.2–3.8, 3.10 | `validFor_length_lt`, `lemma33`, `lemma34`, `lemma35`, `lemma36`, `lemma37`, `gc_decides`, `lemma310`, `lemma310_decides` | `Gradecast.lean` |
| Lemmas 3.11/3.12 | `bc_bb_of_honest_reg`, `bc_bb_of_ba` | `Broadcast.lean` |
| Thm 3.13 (`t < s + ⌈(n−s)/3⌉`, black-box BA) | `theorem313`, `theorem313_solvable`, `resilience_iff` (`⇔ 3t < n + 2s`) | `Broadcast.lean` |
| Thm 3.13 without black box for `n − s ≤ 3` | `theorem313_small` | `Broadcast.lean` |
| Thm 3.14 / Lemma 6.1 (`n − s ≤ 2`, any Byzantine set) | `theorem314`, `theorem314_solvable` | `Broadcast.lean` |
| Thm 4.1 (unregistered sender, `n ≥ 3`) | `theorem41` | `LowerBound.lean` |
| Cor 4.2 (`n ≥ 2`) | `corollary42` | `LowerBound.lean` |
| Counterexamples to Thm 4.1 / Cor 4.2 as printed | `theorem41_false_registered_sender`, `theorem41_false_card_two`, `corollary42_false_card_one` | `Broadcast.lean`, `LowerBound.lean` |
| Thm 5.1 (Π_SBA, black-box authenticated BA) | `theorem51`, `theorem51_unreg`, `theorem51_solvable` | `SimpleBA.lean` |
| Cor 5.2 | `corollary52`, `paper_bound_iff` | `SimpleBA.lean` |
| Else-if reading of Fig. 1 breaks Lemma 3.10 / Thm 3.13 | `Exclusive.lemma310_fails_exclusive`, `Exclusive.theorem313_fails_exclusive` | `Exclusive.lean` |

**Not formalized.**
- The multivalued protocol (full version only).
- Theorem 3.15 (communication complexity).
- Theorem 4.3 (randomized lower bound in the delayed-public-state model) and the shared-coin protocol of §4.3.
- The cited black-box BA protocols (unauthenticated `n > 3t`, authenticated `s > 2t`).

**Trust.**
- No `sorry`. All listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
- Non-vacuity:
  - `theorem313_small` and `theorem314` are unconditional: the black box is discharged by the OR exchange `orBA`.
  - `orBA_boundedAuthBA` gives an instance of Theorem 5.1's hypothesis (only for `s ≤ 2`, where `2t < s` forces
    `t = 0`; `theorem51_unreg_small` uses it with arbitrarily many Byzantine unregistered parties).
  - The lower bounds come with matching positive instances (`theorem314_solvable`, `bb_solvable_card_two`).
- **Where the model comes from.** CSLib provides `Byzantine/LockStep` (`Basic`, `Auth`, `Cover`, `Agreement`).
- **CSLib candidates:**
  - `CoverSystem.scenario_authValid_pa`, the cover lemma for partial authentication (`Model.lean`);
  - `hist_take`, `mem_hist`, `deliver_honest`, `deliver_byz` (`Gradecast.lean`);
  - `firstSome_shift` (`Broadcast.lean`) and `hist_getElem?` (`SimpleBA.lean`).
