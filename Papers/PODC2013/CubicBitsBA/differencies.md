# Differences between the formalization and the paper

Paper: D. R. Kowalski, A. Mostéfaoui, *Synchronous Byzantine Agreement with Nearly a Cubic Number of
Communication Bits*, PODC 2013 (author version hal-01151136).

## Errors in the paper

1. **Theorem 2 (agreement) is false** (`Counterexample.theorem_2_false`, `Counterexample.agreement_fails`,
   and in CSLib's lock-step model `Counterexample.not_solves_BA`). `n = 7`, `t = 2`, correct `0..4`,
   Byzantine `5 = b₁`, `6 = b₂`, binary values, either default value `v0` (the run is parametrized
   by `f = !v0`, all values xor `f`). With `f = false`: inputs `0,0,0,1,1`.
   - Round 1: `b₁` sends `0` to `A = {0,1,2}` and `1` to `{3,4}`; `b₂` sends `1` to everybody.
   - Round 2: to receiver `i`, both Byzantine processes send the echo array with the correct inputs,
     `b₂ ↦ 1` and `b₁ ↦ (the value i received from b₁)`.
   - Round 3: both send an empty suspicion set and echo the round-2 arrays as `i` received them.
   Then `A` decides `0` and `3, 4` decide `v0 = 1` (`decide_exec`). Rule R5: the protocol is the
   paper's specific algorithm (title and abstract), so the verdict is 🚨. Borderline aspect: the
   title is phrased existentially; R5's existential carve-out (→ ❌) does not apply because the
   paper presents this specific protocol as its solution and no repaired protocol with `t + 1`
   rounds and `O(n³ log n)` bits is given (nor known to us). Not degenerate (R2): `n = 7`,
   `t = 2` is inside the claimed range `t < n/3`. Not a typo (R3): repairing it needs a protocol
   change (the round-`(t+1)` information would have to carry suspicions of round-`(t−1)`
   equivocations, or the evaluation would have to use the round-3 echoes as EIG values).
2. **Lemma 5 is false** (`Counterexample.lemma_5_false`): in the run above the set of nodes whose label
   ends with a correct id is a common path covering of the whole tree (`lemma_4`), but the root is not
   common. The failing step is the level-`l ≤ t − 1` case of the proof: "If they do not suspect `p_j`
   this means that they reported the same value `cval(xk)`". The top set only records suspicions
   *reported by round `t`* (and `newval` of level-`t` nodes only sees echoes of reports up to round
   `t`), while an equivocation in round `l` is detected after round `l + 1` and reported in round
   `l + 2`. In the run, `node_b1_not_common` and `children_b1_common`: all children of the node `b₁`
   are common, `b₁` is not.
3. The run also breaks agreement under the alternative reading "at decision time, messages of every
   process suspected at any point are discarded" (checked with the Python simulator
   `simulation/attacks.py`, not in Lean). A different attack (Byzantine `b₂` equivocates its round-3
   suspicion set, `b₃` its round-4 echo) breaks `n = 10`, `t = 3` in the simulator (not in Lean); so
   the failure is not specific to `t = 2`. `simulation/readings.py` replays both attacks under all
   combinations of three non-literal readings of the decision procedure: retroactive discarding of
   suspected senders (`retro`), dropping from a top set the children whose last id the deciding
   process suspects (`excl`), and taking the internal-node majority among non-`⊥` echoes only
   (`nonbot`). The `t = 2` run breaks agreement under the literal and `retro` readings only; the
   `t = 3` attack breaks it under all 8 combinations. Neither alternative reading is in the paper's
   text (§4.2 defines `T` only by `newval = ⊤` and counts all of `T`), so the Lean counterexample
   refutes the protocol as written, and the simulation indicates that these repairs do not help.

## Typos and slips (not affecting the verdict)

- §4.1: "when `val(x)` of some node `x = yjk` is set to `⊤`, this means that `p_k` reported that it
  suspects `p_j`" — inverted; `⊤` means "does not suspect" (as in the bullets).
- §4.2 intuition paragraph: "For the nodes of level 1 and level 2, `val(x)` is a proposed value" — the
  bullets of §4.1 (which we follow) make level-2 `val` a suspicion bit. `val` of internal nodes is not
  used by the evaluation (only in the statement of Lemma 3), so this does not matter.
- Proof of Lemma 5: "`n − 2t > t + 1`" should be "`n − 2t > t`".
- Proof of Lemma 5: the induction hypothesis gives "a child `xℓ` *or one of its ancestors* is common";
  the proof uses "`xℓ` is common". Harmless: the ancestors of `xℓ` are `x` and the ancestors of `x`,
  whose commonness is the claim.
- §6: "relays `(n − 1)t` suspicions" ignores Byzantine processes reporting up to `n − 1` suspicions
  each; the correct bound is about `2nt`, still `O(nt)`.

## Modelling choices

- **Message format.** One record type `Msg` for all rounds; fields unused in a round are ignored by
  receivers, so a Byzantine sender gains nothing from them. "Non-well-formed" messages are modelled by
  `none` (no message) — any well-typed message is well-formed. A round-1 message without a proposal
  (`v1 = none`) is never confirmed.
- **Confirmation.** The round-`r` main part of `j` (round 1: the proposal; round 2: the echo array;
  rounds `≥ 3`: the suspicion set), as received directly by `i`, is confirmed in round `r + 1` iff at
  least `n − t` processes (including `i` itself, and possibly Byzantine ones) echo exactly it. If it
  is not confirmed (or nothing was received), `i` suspects `j` from then on (`susp`, cumulative).
- **`⊥` for suspected senders.** A message from a process suspected *in a previous round* is treated as
  `⊥` (`recv`), literally as in §4. The alternative "retroactive" reading is discussed in Error 3.
- **Echo contents.** Correct processes echo what they received (after the `⊥` rule): round 2 echoes the
  proposals, round 3 the round-2 arrays, round `r ≥ 4` the suspicion sets of round `r − 1`. Echoes are
  not echoed (Remark 1).
- **Decoration (§4.1 bullets).** `val` on levels `2..t` uses reports in rounds `3..t`; leaves use
  reports in rounds `3..t+1` ("did not report"); `cval` on levels `≥ 3` uses echoed reports in rounds
  `4..t+1`; `cval` on level 2 is the round-2 echo; `val` on level 1 the round-1 value.
- **Evaluation (§4.2).** If `|T| < n − t − l` or there is no strict majority, `newval` is `⊥`
  (`false` on levels `≥ 2`, `none` on level 1); the paper states only the positive case, and for
  level 1 says the value is "a proposed value or `⊥`". The root takes a strict majority (`> n/2`) of
  all `n` children; ties and `⊥` majorities give `v0`. The counterexample also works if the root
  majority is taken among the non-`⊥` children only (processes `3, 4` then see `0,0,0,1,1,1`, a tie).
- **`t = 0`.** The level-1 nodes are leaves; we set `newval = val` there, as the leaf rule says.
- **Labels** are lists of distinct ids written in reverse (`ℓ :: k :: y` for the paper's `y k ℓ`).
- **Executions.** `Exec` is a family of views in which correct senders follow `out`; `out` only reads
  earlier rounds (`out_congr`). `Bridge.lean` connects it to CSLib's `LockStep` model (complete graph,
  no self-messages there, so a process recomputes its own messages from its history, `fullView`), and
  `Exec.view_eq` shows executions are determined by the Byzantine messages.
- **Validity statement.** `theorem_1` is the paper's (strong unanimity) validity for multivalued
  consensus with arbitrary `V`; CSLib's `BA` spec uses the same validity.
- **Section 6.** Only the basic protocol is counted, under a fixed-length encoding (`b` bits per value,
  one extra bit per `⊥`-able entry, `n`-bit suspicion sets): `totalBits_le` gives
  `≤ 5n³ + 3n²(b + 1)` bits per correct process, matching `O(n³)` per process for binary values and
  `O(max(n⁴, n³ log k))` in total. The incremental variant (the abstract's `O(n³ log n)`) is only
  sketched in the paper (no precise protocol) and is not formalized; it carries the same information,
  so the counterexample run applies to it as well.
- **Termination** is immediate (decision after round `t + 1`, `validity_termination`).
