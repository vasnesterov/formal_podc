# From Few to Many Faults: Optimal Adaptive Byzantine Agreement — PODC 2026

Andrei Constantinescu, Marc Dufay, Anton Paramonov, Roger Wattenhofer. *From Few to Many Faults: Optimal
Adaptive Byzantine Agreement.* PODC 2026. DOI
[10.1145/3796701.3815964](https://doi.org/10.1145/3796701.3815964). Formalized version: arXiv
[2505.19989](https://arxiv.org/abs/2505.19989) v3 (17 Jun 2026); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The three checked results hold. **Theorem 3.1** (synchronous BA,
`t < n/2`, `O(n·f)` messages, `O(f)` rounds) is proved for the paper's protocol `SyncBA`, with the quadratic
fallback (Momose–Ren) taken as a black box. **Theorem 3.3** (`Ω(t²)` expected messages in asynchrony) holds, in
fact almost surely. **Theorem 3.8** (committee assignment) holds, and we also prove the disperser existence the
paper only cites. The ⚠️ comes from the pseudocode of `ViewByzantineAgreement`: read literally, key proofs do
not certify their view number, and then the lock check can be bypassed. The intended reading (the view is part
of the signed statement) is clear from the proofs. Two proofs (3.3, 3.8) need small repairs.

## Mistakes in the paper

* **Key/lock/commit proofs must sign the view number (pseudocode imprecision; protocol unsafe as written,
  intent evident).** Appendix B.1 forms proofs as `tcombine((KEY, value), ρ)`, without the view. A party then
  stores `key ← (v, view, proof)`, and the key phase compares the *claimed* view of a proposed key with the
  view of its own lock. With unsigned views, a Byzantine leader can re-use a key proof for `v₂` from view 3,
  claim it is from view 9, and pass the lock check of parties locked on `v₁` in view 5. Lemma B.2 then fails,
  and two values can get commit proofs. The paper's proofs speak of "a key proof with view number `view3`" and
  "a commit proof contains a view number", so the view is meant to be signed. Our statements
  `key b v`, `lock b v`, `commit b v` include it (`Stmt`, `key_after_commit`).
* **Theorem 3.3: arithmetic slip in the Markov step (proof repaired; statement true, even stronger).** The
  proof claims `⋂_{p∈C} E_pᶜ ⊆ {M ≥ t²/2}`. With `|C| = t/2` parties each receiving more than `t/2` messages,
  one only gets `M > t²/4`. So `P(⋃ E_p) ≥ 1/2` and "`P(E_p) ≥ 1/t` for some `p`" are unjustified. Positive
  probability is enough for the final contradiction, so the theorem survives. In fact no probability estimate
  is needed: the Final-setup argument applies pointwise to almost every random string. Hence a.s. every
  `p ∈ C` receives more than `t/2` messages, and `M ≥ (⌊t/2⌋+1)(⌈t/2⌉+1) ≥ t²/4` almost surely. The proof
  also silently assumes `t` even (`|C| = t/2`). Its "decides within time `T`" step has no meaning in an
  asynchronous model; we replace it by "decides before receiving any message".
  (`Async.theorem_3_3`, `Async.lower_bound_general`, `Async.no_init_decision`)
* **Theorem 3.8: the proof uses Theorem 6.2 outside its range (proof repaired; statement true).** The proof
  takes a disperser with `N = n` left and `M = 4c_d·f̂·log n` right vertices. Theorem 6.2 is stated only for
  `M ≤ N`, which fails once `f̂` is close to `n / log n`. For `f̂ = 0` the construction has `M = 0` committees,
  so every party is vacuously blocked (degenerate case). We prove the disperser existence directly by a union
  bound, for all `N, M`. This gives Theorem 3.8 for every `n, f̂` with explicit constants: `(4f̂+1)(⌈log₂ n⌉+1)`
  committees, at most `2(⌈log₂ n⌉+1)` committees per party, and at most `4f̂` blocked parties.
  (`theorem_3_8`, `exists_disperser`, `theorem_6_2`)
* **Smaller imprecisions in `SyncBA`** (Appendix B):
  - Whether a party that already has a commit answers `RunRetrieval` is ambiguous. Lemma 10.1 needs every
    honest party to answer an honest leader's retrieval. We take "a party is active in a view iff it had no
    commit when suggesting". Then an honest leader that runs the retrieval sees every honest party active,
    since otherwise it would have received a commit.
  - Line 30 sets the fallback input to `v_in`, which may have become `⊥`; we use the original input. This
    only matters when the honest inputs are not unanimous.
  - Theorem 10.5 says `f < ⌊(n−t−1)/2⌋`, Theorem 7.2 says `f ≤`; `≤` is what holds.
  - `O(n·f)` / `O(f)` are meant with the convention `f ≥ 1` (footnote 2); we state `O(n(f+1))`, `O(f+1)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Theorem 3.1.* CSLib's synchronous lock-step model (`Cslib.Byzantine.LockStep`) on the complete network of
  `Fin n`; one round is one `Δ`. The adversary is static and Byzantine, with `f ≤ t < n/2` parties, rushing,
  and sends arbitrary messages. Signatures are ideal tokens (`LockStep.Auth`): the adversary may forge only
  Byzantine signatures, and may replay any signature an honest party has emitted. A `k`-threshold signature is
  a set of at least `k` partial signatures on one statement. We count messages, not bits; a party gets its
  own messages by self-delivery, which is not counted.
  The protocol `syncBA` is deterministic and defined as a local state machine (`SyncBA/Defs.lean`).
  Stage A runs `ViewByzantineAgreement` with the synchronous retrieval for `n` views of 11 rounds each, round
  robin, so every party leads once, then the `HELP` / `PROOF` / `FALLBACK` / `LOCK` rounds. Stage B runs the
  fallback among the parties holding a fallback certificate.
  The fallback is a hypothesis (`Fallback`): an unforging authenticated BA protocol for `t` faults, deciding
  within `Rfb` rounds, in which every honest party sends at most `mfb` messages whatever the others do. This
  is the paper's Theorem B.15 ("even if not all honest parties join").
* *Theorem 3.3.* Message-driven asynchronous message passing. All randomness, a PKI and any setup are one
  random element `ω`, with no measurability assumed. The scheduler sees only metadata: who sent to whom,
  which messages were delivered, who decided. Faults are static, at most `t` parties, which run the code but
  whose links need not be fair. These are Byzantine behaviours, so a Byzantine-resilient protocol satisfies
  our requirement `Solves`. The weak adversary and scheduler make the lower bound stronger.
* *Theorem 3.8.* Pure combinatorics; `log n` is `⌈log₂ n⌉ + 1`.
* *Weaker than the paper:* Theorem 3.1 is proved against a *static* adversary. The paper claims a dynamic
  one. Correctness transfers for deterministic protocols. For the message bound, messages a later-corrupted
  party sends while still honest are not counted. Local timers / null steps are not modelled in asynchrony.

**Main results in Lean.** (namespace `Podc.FewToManyFaultsBA`)

| Paper | Lean | File |
|---|---|---|
| Theorem 3.1 | `Sync.theorem_3_1` | `SyncBA/Main.lean` |
| Thm B.13 (rounds), Thm B.14 | `Sync.syncBA_correct` | `SyncBA/Correct.lean` |
| Lemma B.11, Thm B.13 (messages) | `Sync.syncBA_msgs` | `SyncBA/Messages.lean` |
| Lemma B.1 (keys) | `Sync.key_unique` | `SyncBA/Safety.lean` |
| Lemma B.2 | `Sync.key_after_commit` | `SyncBA/Safety.lean` |
| Lemma B.3 (agreement of commits) | `Sync.commit_unique`, `Sync.commit_agree` | `SyncBA/Safety.lean` |
| Lemma 10.1 | `Sync.retrieval_fail` | `SyncBA/Validity.lean` |
| Lemmas 10.2, B.4 | `Sync.key_valid` | `SyncBA/Validity.lean` |
| Lemma B.6 | `Sync.view_outcome`, `Sync.propose_success` | `SyncBA/Liveness.lean` |
| Lemmas 10.3, B.7 | `Sync.all_commit` | `SyncBA/Liveness.lean` |
| Lemma B.12 | `Sync.no_fb_of_commit` | `SyncBA/EndGame.lean` |
| Thm B.14 (fallback cases) | `Sync.commit_spread`, `Sync.fb_of_no_commit`, `Sync.finalValue_eq_commit` | `SyncBA/EndGame.lean` |
| unforgeability | `Sync.toks_signed`, `Sync.syncBA_unforging` | `SyncBA/Tokens.lean`, `SyncBA/Main.lean` |
| Theorem 3.3 | `Async.theorem_3_3`, `Async.lower_bound_general` | `AsyncLowerBound.lean` |
| Definition 3.7 | `Compromised`, `Blocked` | `Disperser.lean` |
| Theorem 3.8 | `theorem_3_8`, `theorem_3_8_of_disperser` | `Disperser.lean` |
| Theorem 6.2 | `theorem_6_2`, `exists_disperser` | `Disperser.lean` |

Explicit constants: `syncBA` decides within `11(2f+1)` rounds if `f ≤ ⌊(n−t−1)/2⌋`, else within `11n+3+Rfb`.
It sends at most `22n(2f+1)+3nf` messages, respectively `25n²+n·mfb`. With `Rfb ≤ cR·n` and `mfb ≤ cM·n` this
gives `(47+4cR)(f+1)` rounds and `(100+4cM)·n·(f+1)` messages.

**Not formalized.** Theorems 3.2, 3.4–3.6 and 5.1, the partially synchronous protocol and retrieval
(Section 11), the QAB protocols (Sections 8–11), Theorem B.15 (round/message complexity of Momose–Ren; it is
the `Fallback` hypothesis) and Theorem 6.3.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Sync.theorem_3_1_nonvacuous` shows the hypotheses of Theorem 3.1 are satisfiable. For `t = 0`
the one-round protocol `andBA` is a fallback (`Sync.andBA_fallback`); for `t ≥ 1` no quadratic BA is
formalized. For Theorem 3.3 no asynchronous BA protocol is formalized, so the hypothesis `Solves` is not shown
satisfiable for `t ≥ 1`. Models from CSLib: `Cslib.Byzantine.LockStep` (+ `Auth`, `Sequential`).
CSLib candidates (marked `-- CSLib candidate`): `exists_disperser`, the asynchronous model of
`AsyncLowerBound.lean`, `bScen`/`hist_bScen` (a lock-step protocol run by a subset of the honest parties) and
`sendsAt` (message counting in `LockStep`).
