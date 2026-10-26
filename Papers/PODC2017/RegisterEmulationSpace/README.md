# Space Complexity of Fault-Tolerant Register Emulations — PODC 2017

Gregory Chockler, Alexander Spiegelman. *Space Complexity of Fault-Tolerant Register Emulations.*
PODC 2017. DOI [10.1145/3087801.3087824](https://doi.org/10.1145/3087801.3087824). Formalized version:
arXiv [1705.07212](https://arxiv.org/abs/1705.07212) v1; numbering follows it.

**Verdict: ❌ False claim.** The main results hold: the lower bound of Lemma 1 and Theorem 1,
`kf + ⌈kf/(n−(f+1))⌉(f+1)` registers, is proved, and so are Theorems 3 and 5–7. Three stated claims are false
as written; we prove corrected versions. Two of them, (1) and (3), are slips whose intent is evident; (2) is a missing
hypothesis on the value domain. (1) Algorithm 2 (Theorem 3)
maps client `c_i`, `1 ≤ i ≤ k`, to the register set `⌊i/z⌋`, an off-by-one that overloads one set and breaks
even WS-Safety (Lean counterexample); with `⌊(i−1)/z⌋`, the mapping the paper's own counting describes,
Theorem 3 holds. (2) Theorem 4 (CAS max register is wait-free) is stated for "some domain of ordered values"
but fails for dense domains such as `ℚ`; the proof silently assumes finitely many values below `v`, which
holds for the timestamps the paper uses but not for the stated domain. (3) Theorem 8 read literally (fixed `k`) contradicts Theorem 3; its
intended version (bound independent of `k`) holds. Theorem 2 is proved by a different, direct argument.

## Mistakes in the paper

* **Algorithm 2 as written is not WS-Safe (Appendix D, Theorem 3).** Client `c_i`, `1 ≤ i ≤ k`, writes
  to the register set `R_⌊i/z⌋`. With 1-based `i`, `R_0` gets `z − 1` writers, a later set gets one
  writer more than it is sized for, and when `z | k`, client `c_k` maps to a set `R_m` that does not
  exist. Smallest case: `n = 4`, `f = 1`, `k = 3`, so `z = 2`. Clients `c_2` and `c_3` share the overflow
  set `R_1`, which has `2f + 1 = 3` registers `a, b, c` on servers 0–2. A failure-free sequential run
  goes as follows. `c_2` writes 1 to `a` and `b`, and its write to `c` stays pending. `c_3` writes 2
  to `c` and `a`, and its write to `b` stays pending. Then `c_2`'s old write lands on `c`. A read that
  hears from servers 1–3 sees at most timestamp 1 and returns 1. So the counting of Lemmas 6/7
  ("`⌊(|R_j|−(f+1))/f⌋` writers per set") fails for the paper's own mapping. This is an indexing slip with evident intent
  (the paper says each set serves `(|R_j|−(f+1))/f` clients), but with real consequences. With `j = ⌊(i−1)/z⌋` the algorithm is wait-free and WS-Regular with
  exactly `kf + ⌈k/z⌉(f+1)` registers, so Theorem 3 holds. (counterexample on our formalization of
  Algorithm 2: `Alg2.Counterexample.not_seqSafe_paperMapping`, `not_wsRegular_paperMapping`;
  repaired: `Alg2.theorem3_wsRegular`, `Alg2.theorem3`)
* **Theorem 4 is false for dense value domains (under-specified domain).** Algorithm 1 (max register from one CAS) is
  stated for "some domain of ordered values V". Over `ℚ`, a `write-max(1)` can loop forever while
  another process completes `write-max(1 − 1/(j+2))`, `j = 0, 1, …`, each between the first process's
  read and its CAS. The proof's "assume w.l.o.g. there are `k` values between `v′` and `v`" is an
  unstated hypothesis. The exact condition for wait-freedom is that no interval `[v₀, c)` contains an
  infinite increasing sequence. Lemma 5 (linearizability) and lock-freedom hold over every linear
  order. Theorem 4 holds over `ℕ`, which suffices for the paper's use with timestamps.
  (`MaxRegisterCAS.ratImpl_not_waitFree`, `MaxRegisterCAS.waitFree_iff`; `theorem4_nat`)
* **Theorem 8 is false as literally stated (quantifier slip).** Here `k` is fixed and the function `M` may depend on the
  algorithm. Algorithm 2 (Theorem 3) uses finitely many registers, so it is adaptive with a constant
  `M`. The proof only shows that consumption grows by `f` over each of the `k` writes. True version:
  no `M` independent of `k` works. For every `M` there is a `k` such that every `k`-register emulation
  has a sequential run with more than `M` registers in use. (`theorem8_false_as_stated`; repaired:
  `Alg.theorem8`)
* **Proof gaps in Lemma 1; all statements hold.**
  - *Lemma 3:* the crash run "crashes `Q_i ∪ M_i` immediately after `r`". But in the adversary run,
    reads on these servers keep responding (Definition 3.3(a)), so the two runs differ for `c_i`.
    The servers must crash at the stabilization time. In our version the adversary freezes reads
    too, and its run is then itself fair (`Alg.round_main`).
  - *Lemma 1(b):* the final extension "by Definition 3.3(a)" until `F` is uncovered does not exist
    if `c_i` keeps writing to `F` after it returns. One has to stop scheduling `c_i` and let only its
    pending writes respond (`Alg.lemma1_step`).
  - *Theorem 1:* the last step applies Lemma 1 to `G`, the servers with many registers. But `|G|` may
    exceed `f + 1`, and Lemma 1 needs `|F| = f + 1`. Applying it to `f + 1` servers of `G` repairs
    this (`load_bound`).
  - We simplified the adversary to `G_i = F \ F_i`, which removes `M_i`. We also replaced the paper's
    Lemma 4 by a stronger core statement (`Alg.fresh_resp`): after a complete write of a new value,
    the newly written, previously uncovered registers span more than `f` servers.
* **Lemma 7's first claim is false; the lemma holds.** "Every low-level write triggered after time `t`
  is associated with a bigger timestamp" fails: after `W` returns, an idle writer whose old write
  responds re-triggers (lines 30–32) with its own older timestamp. The conclusion survives, because
  such a re-trigger only re-covers a register that this writer already covered.
  (`Alg2.Lemma7.retrigger_old_timestamp`)
* **Theorem 2's proof is not formalized; the statement is proved directly.** The paper reduces
  Theorem 2 to Theorem 1 by running `2f + 1` copies of the max-register implementation plus
  multi-writer ABD; we did not formalize that composition. We prove Theorem 2 by a covering
  argument instead, with weaker hypotheses: obstruction freedom suffices, and linearizability is
  needed only on `k`-writer executions. It needs a reader distinct from the writers.
  (`MaxRegLB.theorem2`)
* **Superfluous hypotheses and typos.** Theorem 7 does not need `|S| > 2f + 1`. Theorem 1 needs only
  `|S| ≥ f + 1`. Lemma 1 needs only two values, not `k` distinct values. Lemma 1 says "`k`
  failure-free runs `r_i`, `0 ≤ i ≤ k`". Lemma 2.11 writes `δ⁻¹` for `δ`. Algorithm 2's initial state
  `⟨⟨⟨0,1⟩, v₀⟩, …⟩` is ill-typed. The max-register specification "highest written value or `v₀`"
  needs `v₀ = min V`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`; Theorems 2 and 4 use CSLib's shared-memory model instead).
* Asynchronous fault-prone shared memory with servers (Section 2, Appendix A). Clients are arbitrary
  deterministic automata. They trigger low-level reads and writes on base MWMR read/write
  registers `B`, which live on servers `δ : B → S`. They may have several pending operations, and they
  may act between high-level operations. A pending operation takes effect atomically at its
  response. The paper allows earlier linearization of writes but uses this convention in its proof
  (Assumption 1). Restricting runs only strengthens a lower bound.
* Crash failures of clients and of at most `f` servers. Failures are not events: a failure pattern
  enters only fairness (`Alg.Fair`). Crashed clients take finitely many steps. Crashed servers
  respond finitely often. Every pending operation of a correct client on a correct server eventually
  responds, and correct clients are scheduled infinitely often. The scheduler/adversary is
  arbitrary; there is no randomness.
* Hypotheses of the lower bounds. `f`-tolerant obstruction freedom (`Alg.ObstructionFree`, as in the
  paper). Safety only in *sequential* runs (`Alg.SeqSafe`), which is implied by the paper's
  WS-Safety. A `k`-register with writers `w 0, …, w (k-1)` and one further client acting as reader.
  Two distinct values suffice.
* Adversary `Ad_i` (`Round.lean`): a solo strategy for the new writer, which freezes all its
  operations, reads included, on the servers `Q_i ∪ G_i`. We take `G_i = F \ F_i` while
  `|Q_i| < |F_i|`, which simplifies the paper's `M_i`. The frozen set is eventually constant and has
  at most `f` elements. Hence the infinite strategy run is fair with these servers crashed, and
  obstruction freedom applies to it directly (Lemma 3).

**Main results in Lean.** Namespace `Podc.RegisterEmulationSpace`.

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (with extended items (a), (b), (d), (e)) | `Alg.lemma1`, step `Alg.lemma1_step` | `Lemma1.lean` |
| Lemmas 2, 3, Claim 1, Corollaries 1–2 (one round of the adversary) | `Alg.RInv`, `Alg.rInv_step`, `zSet_card_le`, `Alg.round_main` | `Round.lean`, `Lemma1.lean` |
| Lemma 4 (indistinguishability core) | `Alg.fresh_resp` | `Lemma4.lean` |
| Fairness of strategy runs, obstruction freedom ⇒ return | `Alg.fair_solo`, `Alg.exists_ret_of_solo`, `Alg.soloRel_step` | `Runs.lean` |
| Theorem 1 (`|B| ≥ kf + ⌈kf/(n−(f+1))⌉(f+1)`) | `Alg.theorem1` (counting: `load_bound`) | `Theorems.lean` |
| Theorem 5 (`n ≥ 2f+1`) | `Alg.theorem5` | `Theorems.lean` |
| Theorem 6 (`n = 2f+1` ⇒ `k` registers per server) | `Alg.theorem6` | `Theorems.lean` |
| Theorem 7 (`n ≥ ⌈kf/m⌉ + f + 1`) | `Alg.theorem7` | `Theorems.lean` |
| Theorem 8 (repaired: `M` independent of `k`) | `Alg.theorem8` | `Theorems.lean` |
| Theorem 2 (`k`-writer max register needs `k` registers; direct covering proof) | `MaxRegLB.theorem2`, `MaxRegLB.theorem2_of_waitFree` | `MaxRegisterLowerBound.lean` |
| Lemma 5 (Algorithm 1 is linearizable, any linear order) | `MaxRegisterCAS.lemma5`, `MaxRegisterCAS.linearizable` | `MaxRegisterCAS.lean` |
| Theorem 4 over `ℕ` | `MaxRegisterCAS.theorem4_nat`, `MaxRegisterCAS.waitFree_of_locallyFinite` | `MaxRegisterCAS.lean` |
| Theorem 4 fails over `ℚ`; exact condition; lock-freedom | `MaxRegisterCAS.ratImpl_not_waitFree`, `MaxRegisterCAS.waitFree_iff`, `MaxRegisterCAS.lockFree` | `MaxRegisterCAS.lean` |
| Theorem 3: Algorithm 2 (fixed mapping) is wait-free and WS-Regular with `kf + ⌈k/z⌉(f+1)` registers | `Alg2.theorem3_wsRegular`, `Alg2.theorem3` (`waitFree`, `seqSafe`, `wsRegular` for any valid `Layout`) | `Algorithm2*.lean` |
| Algorithm 2 with the paper's mapping is not WS-Safe | `Alg2.Counterexample.not_seqSafe_paperMapping`, `not_wsRegular_paperMapping`, `not_layout` | `Algorithm2Counterexample.lean` |
| Lemma 7, first claim false | `Alg2.Lemma7.retrigger_old_timestamp` | `Algorithm2Lemma7.lean` |
| Theorem 8 false as stated | `theorem8_false_as_stated` | `Theorem8.lean` |

**Not formalized.** The paper's reduction proof of Theorem 2 (multi-writer ABD over `2f + 1` copies); the max-register/CAS rows of Table 1 (ABD with max registers); Section 3.1 (intuition). WS-Safety itself is not defined; the lower bounds assume the weaker `SeqSafe`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: Algorithm 2 satisfies the hypotheses of all lower bounds (`ObstructionFree`, `SeqSafe`) for every `f ≥ 1` and `n > 2f` (`Alg2.theorem3`). For `n = 2f + 1` its register count `k(2f + 1)` matches Theorem 1 exactly. Theorems 2 and 4 use CSLib's `Cslib.SharedMemory` (`Impl`, `Linearizable`,
`WaitFree`/`ObstructionFreeOn`, `Covering`); the rest is self-contained over Mathlib (plus one CSLib
lemma). CSLib candidates: the fault-prone server model (`Model.lean`, `Runs.lean`), `casPrev` (CAS
returning the previous value) and the max-register linearization lemmas `le_resp_of_precedes` and
`resp_le_of_ops`.
