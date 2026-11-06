# Differences between the formalization and the paper

Paper: Delporte-Gallet, Fauconnier, Guerraoui, Kermarrec, Ruppert, Tran-The, *Byzantine Agreement with Homonyms*,
PODC 2011 (HAL hal-00580133v1, with appendix). All theorems and the characterization of Table 1 are true; Prop. 26
is false only for α = 0 and Lemma 34 is unestablished (see Proposition 18); several proofs needed repairs.

## Model (Section 2)

- **Messages.** A correct process sends one `Option M` per identifier and round, to all processes with that
  identifier (the paper: "can direct the message to all processes that have a particular identifier"). A process
  receives its own messages. Byzantine processes deliver arbitrary multisets per recipient, tagged with Byzantine
  identifiers.
- **Numerate/innumerate.** One algorithm class: innumerate = the transition depends only on the set of received
  pairs. Lower bounds are proved for all (numerate) algorithms, upper bounds for innumerate ones (except Prop. 18,
  numerate by design).
- **Restricted Byzantine processes**: per recipient and round, at most `#{b ∈ byz | id b = j}` pairs tagged `j`.
  This is equivalent to "each Byzantine process sends at most one message to each recipient per round".
- **Timing.** Synchronous = `gst = 0`. Partially synchronous = DLS basic model (losses only before `gst`; all
  processes start at round 0 and step every round). The paper's remark that other partial-synchrony models are
  equivalent is not formalized.
- **Decisions.** `Decides p v := ∃ r, decide (state r p) = some v`. Agreement is also required for `p = q`, so
  decisions are stable. An algorithm meeting the paper's first-decision spec can latch its first decision, so the two
  notions of solvability coincide; our algorithms latch.
- **Values.** Lower bounds hold for any value type with two distinct values. Prop. 2 assumes `Nonempty V`, used for
  the default value of the classical black box; Props. 5 and 18 need nothing.
- **Standing assumptions** `n > 3t`, `0 < t < n`, `ℓ ≥ 1` are explicit hypotheses where used. Prop. 4 needs `t > 0`.
  For `t = 0` the partition argument does not apply, and the paper excludes this case. Prop. 5 holds without
  `n > 3t`.

## Proposition 1 (and the lower bound of Theorem 19)

- "It suffices to prove … ℓ = 3t": the reduction (merging identifiers by a surjection `Fin ℓ' → Fin ℓ`) is
  `Solvable.mono_ids`. It needs `n ≥ 3t`, which the standing assumption `n > 3t` gives.
- The cover of Figure 1 is built with two copies of `Fin n`. In copy 0 the processes `k ≥ 3t` form the stack of
  identifier 0; in copy 1 they form the stack of identifier `t`. Segment adjacency is the hexagon
  `Z₁–X₀–Y₀–Z₀–X₁–Y₁–Z₁`. Each scenario uses one copy as its `n`-process system, which avoids cardinality arithmetic.
- **Thm. 19 necessity** is proved with the same cover (innumerate algorithm, restricted Byzantine processes sending
  one copy per identifier), not with the paper's simulation. The paper's proof has a gap (README, Proof gaps),
  repaired either by choosing the clone identifier among correct processes or by our cover argument. Typos in A.4:
  ℓ < 3t (should be ≤), "If ℓ ≥ t" (should be ≤), "less than 3t" (at most 3t). These are typos with evident intent
  (✏️).

## Proposition 2

- The black box `A` is an algorithm of CSLib's classical model (`PartialSync.Algorithm` on `Fin ℓ`, synchronous
  runs `gst = 0`, `δ = 0`). It may send different messages to different processes (the paper: broadcast WLOG). Its
  existence for `ℓ > 3t` is derived (`classicalBA_exists`), not assumed.
- `T(A)` latches the simulated decision (`lat`). The paper instead assumes `A`'s decision is stable, so a correct
  group keeps announcing it. A process decides at most once.
- Line 5's "deterministic choice" is `pick`, a fixed choice on the set of candidate states. Line 8's count is the
  number of distinct identifiers announcing `v`.

## Proposition 4 (and the lower bound of Theorem 20)

- Executions α, β, γ as in Figure 4 (0-based identifiers). The isolated stack of γ gets input `v₀` instead of the
  paper's "2" (irrelevant). Byzantine processes are silent from round T = gst on.
- Thm. 20: the stack processes of α and β are clones (`st_clone`), so one copy per identifier suffices (restricted,
  innumerate), as the paper argues.

## Proposition 5 (Section 4.2, Appendix A.1)

- Each round's output is one record (broadcast init, all echoes, proper set, lock/ack/decide). Lock/ack/decide carry
  no phase tag; receivers interpret them by their own round counter. Phase = 8 rounds: propose at 8ph, lock at
  8ph+2, vote at 8ph+4, ack at 8ph+6, decide at 8ph+7. The leader of phase `ph` has identifier `ph mod ℓ` (0-based).
- Broadcast (Prop. 6): echoes omit the superround tag (every broadcast message carries its phase). Amplification
  applies in every round; accepts are cumulative. Timings match the paper (accepted within the superround after GST;
  relay by the next superround).
- Proper sets: rule 1 counts distinct identifiers in the current round. Rule 2 is read existentially ("some 2t+1
  received sets, no value in t+1 of them"). This is the literal reading of "received proper sets from 2t+1 different
  identifiers and no value appears in t+1 of them" and matches the paper's validity remark, so it is not counted
  as a mistake. Under the universal reading (all received sets) termination fails (README); the paper's termination
  proof needs the existential rule, which would be a local fix. "All values" = `Set.univ`.
- Decisions are latched; the leader decides only its own lock request.
- Proof repairs: Lemma 12 Case 2 (README); Lemma 10's hypothesis weakened to what the proof uses; Lemma 11's tight
  timing (gst ≤ 8·ph₃+6); termination uses leader phases `Q = ℓ(gst+1) + id` of single-process correct
  identifiers. There are at least 2ℓ−n−t ≥ 2t+1 of these, by the strict `n < 2ℓ−3t`. The paper writes `n ≤ 2ℓ−3t`
  and "superround 3" for the ack round (✏️).

## Proposition 16 (Section 5.1, Appendix A.2)

- System: processes `k < ℓ` are Byzantine with identifier `k`; all `n − ℓ ≥ 2` correct processes have identifier 0.
  Any correct process can then be impersonated by Byzantine process 0.
- Configurations = run prefixes. `Dec inp adv k` = decisions in runs extending the prefix (decisions made in the
  prefix included). Lemma 17 is proved for two runs whose correct processes other than `p` agree up to round `k`.
  This is exactly the situation in Lemmas 21 and 22, and it also handles decisions made before round `k`. Valencies
  are for arbitrary value types: univalent = at most one reachable decision.
- The infinite multivalent run is the limit of `advSeq`, built with `Classical.epsilon`.

## Proposition 18 (Appendix A.3)

- One record message per round; the echo table `a` is sent as a function and `init` as a set, so every message is
  "valid" by construction. `a := max(a, initCount, α₁)` instead of overwriting at round 2k, and echo updates apply
  to all k; both are equivalent by Lemma 23. `α₁, α₂ ≤ n`.
- Schedule: phase = rounds 8ph…8ph+7; lock removal uses the accepts of round 8ph+7 (per-superround witnesses, the
  paper's definition). Choices use `pick` on candidate sets.
- Proof repairs: relay holds in every later superround (needed by Lemma 36); Lemma 30 keeps `r ≤ r′` (needed by
  Lemma 35); Lemma 37 Case 2 splits on proper sets (as Lemma 12); proper rule 2 is existential; termination uses
  the deterministic choice on the common set of lock requests.
- **Lemma 34 ("locks contain at most one pair at the end of each phase") is unestablished, not formalized (❌).** Its
  proof assumes that at lines 24–26 the process still has line 16's `n−t` witnesses. With per-superround witnesses
  (the paper's definition; Lemma 36 needs those of superround 4 at lines 24–26, our reading) this fails before T:
  the echoes of the last round can all be lost, so an older lock with another value survives. Reviewer's hand-built
  run (not in Lean): `n = ℓ = 4`, `t = 1`, Byzantine `b`; `p` locks `v′` in phase ph′ (votes of `p`, `q₁`, `b`; the
  messages to `q₁` in its lock round are lost), later `q₁`, `q₂`, `b` propose and vote `v`, `p` locks `v`, and all
  echoes to `p` in superround 4 are lost, so `p` ends the phase with two pairs. Under a cumulative reading of
  witnesses (all accepts so far, max multiplicity per identifier) the paper's proof of Lemma 34 is correct; Lemma 30
  (unforgeability bounds every accept) and Lemma 36 (relay) should survive it, but that variant is not formalized.
  Lemma 34 is not used: Prop. 39 only needs that some lock `(v₁, ∗)` is held (line 6 then excludes all other values),
  `decAt_agree`. The lemma is neither proved nor refuted, and the pseudocode admits a reading under which it holds.
- Prop. 26 is literally false for α = 0 (it demands an Accept when nobody broadcast; Figure 6 accepts only after
  `n−t` echoes). It is a degenerate case (✏️), never used with α = 0 (the paper's Lemma 24 itself separates α > 0).
  We prove the witness form `cc_le_witnesses` (summed over identifiers: correct broadcasters ≤ witnesses in round 2k+1 after GST); its proof
  gives the per-identifier bound `α ≤ α′` for every identifier.
- Lemma 33's proof cites "Lemma 22" (means 32). Prop. 25 (unicity) holds by construction.

## Theorems 3, 13, 14, 15, 19, 20

Stated as `iff`s in `Main.lean` under `n > 3t`, `ℓ ≥ 1` (and `t > 0` for 13, 20), with two distinct values. The
introduction's example (t = 1, ℓ = 4: solvable for n = 4, not for n = 5) is `intro_example_four` /
`intro_example_five`.
