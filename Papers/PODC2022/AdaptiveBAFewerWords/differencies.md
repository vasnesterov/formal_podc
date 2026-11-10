# Differences between the formalization and the paper

## Versions

- **Judged: the PODC 2022 brief announcement (June 2022).** It claims the first BB with `O(n(f+1))` words for
  `n = 2t + 1`. It contains Definitions 2.1–2.2 and Algorithms 1–2 (identical to v2, including line 23), and
  no proofs. The adaptive weak BA the claim needs is deferred to the full version [7] = arXiv 2202.09123,
  which was then **v1** (18 Feb 2022).
- **v1's weak BA** (Algorithms 3–4) has no commit levels:
  - a process commits only to the first commit certificate, but sends `decide` for every certificate the
    leader relays (line 43 unconditional);
  - it runs `t + 1` phases (also in the text and in Lemma 6.2's proof);
  - lines 25–28 set `decision ← ⊥` at processes that decided before the fallback.

  The authors replaced it in **v2** (10 Jan 2024) after Elsheimy et al. found an error.
- **Formalized: v2** (the authors' corrected weak BA); numbering follows v2. All Lean counterexamples refute
  **v2**. For v1 we checked by hand, not in Lean:
  - the hand-off attack (`lemma19_false`) applies verbatim, since lines 5–24 and the proof of Lemma A.6 are
    identical;
  - a commit-certificate attack applies with `n = 7`, `t = 3`, Byzantine `p1`, `p2`, `p4` (see README);
  - the `t + 1`-phase run of `lemma6_false_printed_phases` refutes v1's Lemma 6.2 (there it is not a slip).

## Mistakes (labels of `mistakes-labeling.md`)

1. ❌ **Theorem 5 / Lemma 15 / Lemma 20 (weak BA agreement): commit levels.** Line 47 stores the level of the
   relayed certificate, not the phase; a Byzantine leader relays an old commit certificate after harvesting a
   higher-level one on another value. `theorem5_false` (`n = 5`, `f = 2`, `t + 1` or `n` phases, all readings
   of lines 15/37/48), `theorem5_false_small_f` (`n = 11`, `t = 5`, `f = 2 < (n−t−1)/2`), `lemma15_false`.
   No repair formalized.
2. ❌ **Lemma 19 (hand-off).** A decision taken at line 14 (help answer) is not broadcast with its proof; the
   fallback can contradict it. `lemma19_false` (`n = 3`, `f = 1`, all readings of lines 1, 15, 33, guard).
3. 🔧 **Lemmas 9, 11 (Algorithm 2 line 23).** The leader relays only sender-signed values, not idk
   certificates. `BB.Counterexample.lemma9_false`, `lemma11_false`, `keyFact_false` (Section 5.1's "later
   correct-led phases are silent" also fails). Repaired rule (relay any `BB_valid` value): `BB.lemma9`–`lemma12_*`,
   `BB.theorem13`, `BB.words_le`.
4. 🔧 **Lemma 16, last clause** ("this decision is a proposal of a correct process") is false (a relayed commit
   may be on a Byzantine proposal); unused. `lemma16` proves the rest.
5. ✏️ Algorithm 3 line 1 loops `t + 1` times; text says `n`. `lemma6_false_printed_phases` / `lemma6_n_phases_ok`;
   we use `n` for `lemma6`, `words_le`.
6. ✏️ Algorithm 3 line 15 `bu_decision ← decision` (undecided processes fall back on `undecided`):
   `lemma22_false`; intended reading `lemma22_intended_ok` (parameter `intendedBu`).
7. ✏️ Algorithm 5: `bu_decision` initialised to `⊥` and overwritten at line 19 (formalized: input unless
   decided); line 26 echoes `bu_proof = ⊥` for decided processes (`printed_noProof_disagreement`; formalized:
   attach `proof`).
8. ✏️ Strict loop condition `fallback_start > now` (Alg. 5 line 20, Alg. 3 line 16) drops a message arriving
   exactly at the deadline (`strictWindow_disagreement` for Algorithm 5); we use the closed window.
9. ✏️ Leader rounds unguarded (Alg. 4 lines 37, 48; Alg. 2 lines 22–27): a "silent" correct leader relays
   unsolicited Byzantine messages. `unguarded_silent_phases_cost` (132 words vs. 49). Formalized: guarded
   (parameter `guard` in the weak BA model; the BB model is guarded).
10. ✏️ `BB_valid` ("signed by `t + 1` processes") read as "sender-signed or `QC_idk(j)`" (`bbValid`).
11. ✏️ Definition 3 leaves implicit: correct inputs are valid (stated in Section 5), and a correct process only
    decides values that exist in the run (automatic with unforgeable signatures). Both are hypotheses of the
    black box (`WeakBASpec`).

## Readings and modelling choices

- **Line 33 "for the first time"**: parameter `voteOnce`. Per phase (`false`, needed by the proof of Lemma 16)
  is used for `lemma16`, `lemma6`, `words_le`, `theorem5_false`. Once per run (`true`): Lemma 16/6 fail
  (`lemma16_lemma6_false_voteOnce`), and agreement still fails by `lemma19_false`.
- **Static corruption** instead of adaptive: the protocols are deterministic; an adaptive adversary is simulated
  by corrupting the final set from the start. Counterexamples use static adversaries (a special case).
- **Lock-step rounds** for Algorithms 1–4 and rounds 1–5 of Algorithm 5; the post-phase part of Algorithm 3 is
  lock-step too (H1–H3). The fallback window of Algorithm 3 is abstracted: if any correct process forms or
  receives a fallback certificate, all correct processes run the fallback (Lemma 17); an undecided process adopts
  a value carried with a valid proof by a former's message (line 11) or by a Byzantine message (relayed by
  echoers), the first one in a fixed order (this restricts the adversary, so it is sound for counterexamples;
  no positive result about this part is claimed). Algorithm 5's hand-off uses real discrete time with delays in
  `[0, δ]` and first-hearing times by reachability (`Hears`).
- **Signatures**: ideal, symbolic; unforgeability as `AdvValid` (rushing, eavesdropping adversary: a share is
  usable once some correct process has sent it). Certificates carry their level/phase, so "level valid according
  to `QC_commit`" holds by construction. Correct processes accept the first message per channel and round.
- **Leader tie-breaks**: a correct leader relays the first commit of maximal level (Algorithm 4), takes the first
  value with enough votes/decides; Algorithm 5's leader prefers `0`; Algorithm 2's leader the first valid reply.
- **Black boxes**: the weak BA in the reduction (`WeakBASpec`: agreement, termination, unique validity, decided
  values exist, under valid inputs; `Ex` = inputs of correct processes ∪ items the adversary can produce at any
  round, which assumes the weak BA does not make correct processes sign `⟨idk, ·⟩`); `A_fallback` as a strong
  BA on outcomes (Algorithm 3: one common output `fbOut` with strong unanimity; Algorithm 5: `FallbackSpec`,
  conditional on all correct processes starting at most `δ` apart).
- **Lemma 18**: only its timing content is proved. That the skewed run is a correct run of `A` is assumed
  (black box). We note that windows overlap (`windows_overlap`: round tags needed) and that the skew gives
  Byzantine processes a one-round look-ahead on early starters (`skew_lookahead`), stronger than a rushing
  lock-step adversary; the paper does not address this.
- **Resilience**: the reduction is proved for `n ≥ 2t + 1`; the weak BA results assume `n = 2t + 1`; Lemma 6 uses
  `q + f ≤ n`, implied by `f < (n − t − 1)/2`.
- **Phase leaders**: `p_{j mod n}` is the `Fin n` index `j % n` (so `p_0` leads phase `n`).
- **Word counts**: one word per message, messages to oneself included; Algorithm 3's count covers the phases and
  rounds H1–H2 (`5n + 2nf` and `nf`), Algorithm 1's round 1 and the phases (`n(f+4)`), Algorithm 5's rounds 1–5
  and the hand-off (`4n` when `f = 0`). The fallback's own `O(n²)` is not counted.
- Decided processes in Algorithm 5 never leave the `while` loop (they decide but do not halt); harmless.
- `decide_proof` is overwritten by later phases (Algorithm 3 line 2); modelled literally (a help answer is valid
  only if its proof matches the decision).
- Algorithm 3 line 11's `proof` is read as `decide_proof`.

## Not formalized

Lemma 14 (validity of phase decisions); a repaired weak BA; Momose–Ren; the fallback's cost.
