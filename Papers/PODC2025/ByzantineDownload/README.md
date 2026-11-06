# Distributed Download from an External Data Source — PODC 2025

John Augustine, Soumyottam Chatterjee, Valerie King, Manish Kumar, Shachar Meir, David Peleg. *Brief
Announcement: Distributed Download from an External Data Source in Byzantine Majority Settings.* PODC 2025.
DOI [10.1145/3732772.3733526](https://doi.org/10.1145/3732772.3733526). Formalized version: the full version,
arXiv [2412.19649](https://arxiv.org/abs/2412.19649) v1 ("… in Faulty Majority Settings", the only version);
numbering follows it.

**Verdict: ⚠️ Weakened.** The deterministic crash-tolerant **Rapid Download** protocol (Algorithm 7) is wrong: with
`k = 4` peers, `n = 4` bits and `f = 2` crashes, a nonfaulty peer finishes without ever learning a bit, so Lemmas
5.13 and 5.15 are false and Theorem 5.16 (time `O(n + f)` for any `β < 1`) is unestablished for `f ≥ 2`. The
one-round lower bound (Theorem 3.6) and the simple **Static Download** protocol (Theorem 5.9: query-optimal, time
`O(nf)`) are correct, after small repairs of their proofs. The paper's main point, the randomized protocols against
Byzantine peers, was not checked.

## Mistakes in the paper

### ❌ Algorithm 7 (Rapid Download), Lemmas 5.13 and 5.15
Algorithm 7 does not solve Download: with `k = 4` peers, `n = 4` bits and `f = 2` crashes
(`β = 1/2`), a run makes the nonfaulty `M3` skip bit 2 and finish with `res[2] = ⊥`, which refutes
Lemmas 5.13 and 5.15 (`Rapid.lemma_5_13_false`, `Rapid.lemma_5_15_false`,
`Rapid.rapid_not_solves`).

**Impact.** Theorem 5.16 (time `O(n + f)` for any `β < 1`) is unestablished for `f ≥ 2`. The lower
bound (Theorem 3.6) and Static Download (Theorem 5.9) are unaffected.

**Details.** Peers `M0,…,M3`, `lead(v) = v mod 4`; `M1` and `M2` crash (`f = 2 ≤ βk` with
`β = 1/2`). In the run below, "index" is the paper's 1-based bit index.
- **View 1** (leader `M1`). `M1` sends `⟨view 1, 1, b₁⟩` to all, then crashes during its second
  transmission, which reaches only `M2`. `M2` now has two messages, sets `I = 2` and sends
  `⟨view change 2, 2⟩`. `M0` and `M3` see the silence and send `⟨view change 2, 1⟩`. All three
  messages reach `M2` in the same round, so `M2` works on index 2.
- **View 2** (leader `M2`). `M2` queries `b₂` and crashes during its first transmission, which
  reaches only `M0`; `M0` sets `I = 2`, `res[2] = b₂`. `M3` heard nothing, so it suspects `M2` one
  round earlier than `M0` and sends `⟨view change 3, 1⟩` to `lead(3) = M3`, i.e. to itself.
- **View 3** (leader `M3`). `M3` starts when its own message arrives. Line 8 takes the highest
  index among the view-change messages of *that round only*, which is 1. `M0`'s
  `⟨view change 3, 2⟩` arrives one round later and is ignored ("for the first time", line 7). `M3`
  sends `⟨view 3, 1, b₁⟩` twice. `M0` keeps `I = 2` (line 19: `1 < 2`), but on the second message
  line 23 increments `I` to 3 regardless of the index carried.
- **The skip.** At this point the nonfaulty `M0` has `I = 3`, while the nonfaulty `M3` has
  `res[2] = ⊥`; this refutes Lemma 5.13. From now on every leader works on index `≥ 3`. `M3`
  downloads bits 3 and 4, finishes with `I = 5 > n`, and keeps `res[2] = ⊥` forever, which refutes
  Lemma 5.15 and the correctness of Algorithm 7.

The pseudocode is event-driven and does not fix initialisation or timing. We fix the round timing
of the paper's own Remark 1 (also Remark 2's claim "M will work on `i+1`" fails here). Under the
other natural timing (a view-changing peer stays idle for two rounds), a simulator finds the same
index skip with `n = 6`, caused by different `F` sets instead of different detection times. With
Remark 1's timing, the protocol still fails (simulation, `n = 6`) if a leader adopts a higher index
that arrives later, as Remark 2 suggests. The theorem's `f ≤ βk`, `β < 1` (also claimed in §1.4.3)
contradicts Table 2, which marks Theorem 5.16 "#: `β ≤ 1/k`", i.e. `f ≤ 1`.

### ✏️ Slips
- Algorithm 7 never says how view 1 starts: no peer sends `⟨view change 1, ·⟩`, so read literally all
  peers suspect the nonfaulty `lead(1)` after one round, contradicting Lemma 5.11. The intent is evident: we let
  `lead(1)` start view 1 at time 0.
- Theorem 5.9 for `f = 0`: `T = O(nf)` is literally false (it is `n`), and so is `M = O(k²·f·n)`; the bounds hold
  for `f ≥ 1`.
- Peer IDs are `[1, k]` but `lead(v) = v mod k ∈ [0, k−1]`.

### Typos
- In §3 the letter `n` is both the number of peers and of bits, and Lemma 3.3 needs them equal.

## Proof gaps (statements true)

### 🔧 Theorem 3.6 (Eq. (8) in the proof of Lemma 3.4)
Eq. (8) claims `p(R̂(Byz)) > (1 − e⁻¹)/2` *for every* Byzantine set `Byz`, which fails, e.g., when
the defective peer `v(R)` always lies in `Byz`.

**Impact.** Statement true; we prove a derandomized version (`theorem_3_6`).

**Details.** Only the average over the uniformly random `Byz` is bounded. That suffices once the
involution `Byz ↦ V \ (Byz ∪ {v(R)})` is applied per random profile `R`; the paper applies it to
sets that depend on `R`.

**Repair.** For every algorithm there are an input, a bit `ℓ` and a fixed set of `(n−1)/2`
Byzantine peers that run the algorithm on the input with `ℓ` flipped, with failure probability
`≥ (1 − e⁻¹)/4`.

### 🔧 Lemma 3.3 (maximizing `q(i)`)
The claim "q(i) is maximized when `p_v(i) = 1/n`" is not justified.

**Impact.** Statement true; we use `1 − x ≤ e^{−x}` and pigeonhole instead (`lemma_3_3`).

### 🔧 Theorem 5.9 (query bound)
The proof says each nonfaulty peer leads "at most `n/γk`" views, but the exact bound is
`(n + k − 1)/(k − f) ≤ 2n/(γk)`.

**Impact.** Statement true: the exact bound still gives `Q = O(n/γk)` (`theorem_5_9_queries`, `Static.theorem_5_9`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Crash part** (`Model.lean`): synchronous DR model with `k` peers on a clique and a trusted source
  `X : Fin n → Bool`. A round is a query sub-round, the answers, then a message sub-round (a message to
  each peer, possibly oneself), followed by a local step. Protocols are deterministic state machines.
  Crash faults follow an arbitrary pattern: a peer crashing in round `c` sends its round-`c` messages only
  to an adversarial subset of peers and then stops. At most `f` peers crash. The adversary chooses the
  input and the pattern, which for deterministic protocols is the same as an all-knowing adversary.
  `Q` is the number of bits a nonfaulty peer queries. Download within `T` means: from time `T` on, every
  nonfaulty peer has `res = X`.
* **Lower bound** (`LowerBound.lean`): one synchronous round; `n` peers and `n` bits. Each peer has
  independent private coins over a finite space, and its query set, messages and output are arbitrary
  functions of its coins, its answers and its inbox. Each peer always skips at least one bit
  (`A ∈ A(n−1, 1)`). The adversary is the paper's weak adversary, derandomized: a fixed input, bit `ℓ` and
  set of `(n−1)/2` Byzantine peers that run the algorithm honestly on the input with bit `ℓ` flipped. The
  result is stronger than with the paper's random set, and it also covers the broadcast model.
* **Algorithm 7** (`RapidDownload.lean`) is encoded literally from its pseudocode, with the timing and
  initialisation choices listed in `differencies.md`. A crash-free sanity run downloads all bits.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.3 | `LowerBound.lemma_3_3` | `LowerBound.lean` |
| Claim 3.5 | `LowerBound.claim_3_5` | `LowerBound.lean` |
| Lemma 3.4 / Theorem 3.6 | `LowerBound.theorem_3_6` | `LowerBound.lean` |
| Theorem 3.6, broadcast model | `LowerBound.theorem_3_6_broadcast` | `LowerBound.lean` |
| Algorithm 6 | `Static.alg` | `StaticDownload.lean` |
| Lemma 5.2 | `Static.lemma_5_2` | `StaticProof.lean` |
| Cor. 5.3, Lemma 5.4, Cor. 5.6, 5.8 (one view, in sync) | `Static.view_step`, `Static.σs_inv` | `StaticProof.lean` |
| Lemma 5.7 | `Static.lemma_5_7` | `StaticProof.lean` |
| Theorem 5.9 (`Q ≤ 2n/γk`, `T = (n+f)(f+1)`, `≤ (k−1)(n+f)(f+1)` messages per peer) | `Static.theorem_5_9` (parts: `theorem_5_9_correct`, `theorem_5_9_queries`, `theorem_5_9_messages`) | `StaticProof.lean` |
| Round-robin leader counting (proof of Thm 5.9) | `roundRobin_count` | `Counting.lean` |
| Algorithm 7 | `Rapid.alg` | `RapidDownload.lean` |
| Lemma 5.13 — **false** | `Rapid.lemma_5_13_false` | `RapidDownload.lean` |
| Lemma 5.15 — **false** | `Rapid.lemma_5_15_false` | `RapidDownload.lean` |
| Algorithm 7 solves Download (Thm 5.16's proof) — **false** for `f = 2` | `Rapid.rapid_not_solves` | `RapidDownload.lean` |

**Not formalized.**
* The Byzantine randomized protocols (§2, §4), the asynchronous crash protocols (§6) and message sizes.
* A proof of Algorithm 7 for `f ≤ 1`: for `f = 1`, exhaustive simulation (`k ≤ 4`, `n ≤ 4`) found no failure;
  this is not a proof.
* Whether some protocol achieves Theorem 5.16's bounds for `f ≥ 2`: the existential theorem may still hold
  with a repaired protocol, which is not settled.
* Lemmas 5.10–5.12 and 5.14 individually.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The Algorithm 7 counterexample is checked by `decide +kernel` on a memoized execution
(`tab`, `cfg_eq_tab`), with no `native_decide`. `rapid_crashFree` is a sanity check of the encoding:
without crashes, all 4 bits are downloaded and each peer makes one query. The model is paper-local and
does not reuse CSLib's `SyncCrash`, because the source and the query sub-rounds do not fit its
history-based protocols.
