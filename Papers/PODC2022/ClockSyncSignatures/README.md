# Approximate Agreement with Signatures (from Optimal Clock Synchronization with Signatures) — PODC 2022

Christoph Lenzen, Julian Loss. *Optimal Clock Synchronization with Signatures.* PODC 2022. DOI
[10.1145/3519270.3538444](https://doi.org/10.1145/3519270.3538444). Formalized version: arXiv
[2203.02553](https://arxiv.org/abs/2203.02553) v2; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** We checked only Section 2.1, the synchronous approximate-agreement algorithm APA built on
signature-based crusader broadcast; the clock-synchronization results (Sections 3 and 4), the paper's main point, are
not formalized. Lemma 7, Lemma 8, Theorem 9 (2 rounds, `(ℓ, ℓ/2, ⌈n/2⌉−1)`-secure) and Corollary 2
(`2⌈log₂(ℓ/ε)⌉` rounds) are all true, apart from a degenerate corner of Corollary 2. The one real error is the
induction step of Lemma 8, which a few lines repair.

## Mistakes in the paper

### ✏️ Slips
- Corollary 2 (round count): for `ℓ ≤ ε` the count `2⌈log(ℓ/ε)⌉` is zero or negative, and undefined for `ℓ = 0`. Zero
  rounds suffice there (`corollary_2`).
- Corollary 2 and Figure 4 (repetition of APA): repeating the algorithm needs signatures tied to the instance. Figure 4
  signs only `b_v`, so without a session id an old signature of an honest dealer can be replayed, and CB validity
  fails. The paper's "(an instance of) Algorithm CB" implies separate signing domains; our tokens carry the iteration
  number (`corollary_2`).
- Lemma 7's proof: the upper indices are off by `b`. The retained maximum is the `(n − f)`-th smallest value in both
  lists, not `r̃^{n−(f−(b−1))}` and `r^{n−(f−b)}`. The inequalities used are correct.
- Definition 6 and Algorithm CB (Figure 4) are stated for binary inputs `b_v ∈ {0, 1}`. APA uses them for
  real values. Signatures work for any message, and we formalize CB on reals directly.

### Typos
- Lemma 7's proof writes the lists with lengths `n − k` and `n − k + 1` instead of `n − b` and `n − b + 1`.

## Proof gaps (statements true)

### 🔧 Lemma 8 (induction step written backwards)
The induction step concludes `x ∈ I_w ⊇ Ĩ_w`, where `Ĩ_w` is the interval *with* the extra `⊥`, but Lemma 7 gives the opposite inclusion, and the step goes from a `k`-execution to some `(k+1)`-execution instead of covering every one.

**Impact.** The step as written proves nothing, but the lemma holds with a repaired induction (`lemma_8`).

**Details.** The induction is on the number `k` of `⊥` values received by honest nodes. The paper starts from
a `k`-execution and replaces one value by `⊥`. Lemma 7 says that a `⊥` *enlarges* the interval, so the
correct step is `x ∈ I_w ⊆ Ĩ_w`. To cover every `(k+1)`-execution, one must start from an arbitrary
`(k+1)`-execution and remove a `⊥` (honest `w`, faulty dealer `d`). The `⊥` must be replaced by the value the
other honest nodes got from `d` (any value if all of them got `⊥`). Only then does the `k`-configuration still
satisfy crusader consistency, so that the induction hypothesis applies. The closing sentence "this
construction applies for any inputs … the claim follows for all executions" leaves this out.

**Repair.** The induction runs over configurations of CB outputs that satisfy validity and crusader
consistency. A direct argument via order statistics of the common values would also work.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous lock-step rounds (CSLib `Cslib.Byzantine.LockStep`) on the complete network of `n = |P|` nodes.
  Static Byzantine set of at most `f` nodes (`atMost f`). Reliable channels. Deterministic protocol. No
  randomness.
* Ideal signatures as CSLib tokens (`LockStep.Auth`). A token `(d, j, v)` is `d`'s signature on "my value in
  iteration `j` is `v`". Honest nodes are `Unforging` (proved: `alg_unforging`). The adversary
  (`Scenario.AuthValid`) is rushing and eavesdropping. It can send any token signed by a corrupted node, or any
  token an honest node has emitted in this round or earlier. This is the paper's "rushing adversary that cannot
  forge signatures". Corollary 2 "repeats the algorithm" with fresh CB instances. This needs signatures
  tagged with the iteration number (a session id). Without the tag, the adversary can echo an honest dealer's
  signature from an earlier iteration and make honest nodes output `⊥` for an honest dealer, which breaks CB
  validity. Our tokens carry the iteration number.
* `alg f K` runs `K` iterations of APA, two rounds each (the two rounds of Algorithm CB). All `n` CB instances
  run in parallel. After round `2K` every node decides its last value. CB at node `w` for dealer `d`: output
  `⊥` if `d`'s token is invalid or missing, or if an echo carries a valid signature of `d` with a different
  value; otherwise output the signed value. A node counts its own received token as one of the echoes, which
  is the paper's "send to all nodes" including itself.
* Specification (Definition 1): `AASpec ℓ ε`. If the honest inputs have range `≤ ℓ`, then every honest node
  decides, decisions lie between two honest inputs, and honest decisions are pairwise `≤ ε` apart. `Secure t ℓ ε
  A T` adds unforgeability of `A` and termination within `T` rounds against all admissible adversaries.
* The combinatorial layer (`APA.lean`) assumes only the CB properties of Definition 6 (`IsCrusader`). It applies
  to any CB implementation.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm APA (Figure 1): retained values, interval, midpoint | `kept`, `lo`, `hi`, `interval`, `apaOut`, `mem_kept_bounds` | `APA.lean` |
| Lemma 7 | `lemma_7`, `lemma_7_subset` | `APA.lean` |
| Lemma 8 (repaired induction) | `lemma_8` | `APA.lean` |
| Theorem 9, combinatorial core (validity, `ℓ/2`-consistency) | `theorem_9_core`, `apa_step` | `APA.lean` |
| Algorithm CB (Figure 4): validity and crusader consistency (any number of faults) | `cb_isCrusader` | `Protocol.lean` |
| Theorem 9: APA is a 2-round `(ℓ, ℓ/2, ⌈n/2⌉−1)`-secure protocol | `theorem_9` | `Protocol.lean` |
| Corollary 2: `(ℓ, ε, ⌈n/2⌉−1)`-secure in `2⌈log₂(ℓ/ε)⌉` rounds | `corollary_2` | `Protocol.lean` |
| `K` iterations for any `f` with `2f < n` (generalization) | `alg_secure` | `Protocol.lean` |

**Not formalized.** Section 3 (Crusader Pulse Synchronization: Theorem 4 / Corollary 4, Lemmas 10–16, real-time
clocks and drift) and Section 4 (the `2ũ/3` lower bound, Theorems 5/17, Lemmas 18–19).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
model comes from CSLib (`Byzantine.LockStep.{Basic,Auth,Agreement}`, `Byzantine.Specs`) and the range
contraction from `ApproxConsensus.Contraction`. The order-statistics library is staged in
`Podc/Foundations/Data/Multiset/OrderStatistic.lean` (CSLib candidate). Non-vacuity: `alg_unforging` shows
that the protocol meets the honest-node side of the signature model; `exists_authValid` shows that for every
Byzantine set and every input vector some reliable, unforgeability-respecting scenario exists (silent corrupted
nodes), so the adversary hypotheses of `Secure` are satisfiable.

**CSLib candidates.** `Podc/Foundations/Data/Multiset/OrderStatistic.lean` (`Multiset.orderStat` and counting
lemmas; HybridApproxAgreement's `kth` could migrate to it).
