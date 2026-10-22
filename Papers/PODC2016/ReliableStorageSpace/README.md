# Space Bounds for Reliable Storage — PODC 2016

Alexander Spiegelman, Yuval Cassuto, Gregory Chockler, Idit Keidar. *Space Bounds for Reliable Storage:
Fundamental Limits of Coding.* PODC 2016. DOI [10.1145/2933057.2933104](https://doi.org/10.1145/2933057.2933104).
Formalized version: arXiv [1507.05169](https://arxiv.org/abs/1507.05169) v1 (the only arXiv version); numbering
follows it.

**Verdict: ❌ False claim.** Algorithm 2 (Section 3.1, the safe erasure-coded register) is not safe as
written when `k ≤ f`, e.g. for replication with `n = 3`, `f = 1` (Lean counterexample). With the reader decoding
the largest qualifying timestamp, Corollary 3 is proved. Theorem 1 ("every write adds at least `log₂|U_s|` bits")
is false as stated, and it does not justify the storage model the paper builds on it: "every stored bit
belongs to one write". The main lower bound (Theorem 2, Corollary 2: unbounded storage, or a time when `f + 1`
objects each hold `D` bits of one write) is proved in that model, the paper's own, after several repairs. Whether
it holds for algorithms that code across writes is open.

## Mistakes in the paper

* **Algorithm 2 (Section 3.1) is not safe as written when `k ≤ f`; Lemma 9's proof misses this.** Line 16 lets the
  reader decode *any* timestamp that has `k` pieces among its `n − f` responses. Take replication (`k = 1`,
  `n = 3`, `f = 1`), which the paper explicitly allows. Write `w₁` stores on objects 1 and 2 and returns. Then `w₂`
  reads objects 1 and 2, stores on 2 and 3, and returns. A later read hears from objects 1 and 2. Both timestamps
  have one piece, so the reader may return `w₁`'s stale value. This violates safety, since the read has no
  concurrent write. For `k > f` a stale timestamp cannot collect `k` pieces, and choosing the *largest*
  qualifying timestamp fixes every case. With that fix Corollary 3 holds: Algorithm 2 is wait-free and strongly
  safe, and it stores at most `n` pieces. (counterexample with the "smallest qualifying timestamp" reading:
  `Safe.not_stronglySafe`, `Safe.not_weakRegular`; repaired: `Safe.corollary3`)
* **Theorem 1 is false as stated.** It claims that a write of `u_s ∈ U_s` to a base object that keeps all
  written values recoverable adds at least `log₂|U_s|` bits. Take `|U₁| = 5` and `|U₂| = 3`, and let the object
  store the minimum each time: `⌈log₂ 5⌉ = 3` bits after the first write and `⌈log₂ 15⌉ = 4` after the second.
  The second write adds one bit, less than `log₂ 3`. With padding, a write can add no bits at all. The proof
  subtracts two lower bounds, which is invalid. Its induction hypothesis ("the object stores exactly
  `log₂(|U₁|⋯|U_{s−1}|)` bits") assumes minimal storage. The statement holds only for minimal encodings and
  power-of-two set sizes, the simplification made in Lemma 1's proof. What is true in general is the cumulative
  bound of Lemma 1. (`theorem1_false`; true version `theorem1_cumulative`)
* **The storage model ("each stored bit is associated with a particular write") is assumed, not proved.** Section 4
  adopts this model explicitly ("in the sequel we can assume without loss of generality …"), and we formalize
  Theorem 2 and Corollary 2 in it. The "without loss of generality" is not justified. The paper derives it from
  Theorem 1, but even the correct cumulative version does not give it. Lemma 1 concerns one object that must keep
  *all* its inputs recoverable from its own bits. A register emulation may discard old values, spread a value
  over several objects, or store functions of several values (e.g. `v₁ ⊕ v₂`). Section 4's bookkeeping (`C⁺`,
  `F(t)`, Observation 1, Lemma 3) depends on this attribution. Our black-box model makes it hold by construction:
  values are opaque, and stored data are blocks, each a fixed function of one written value, which clients only
  copy. Re-encoding another client's value is excluded as well. So the abstract's "any reliable storage
  algorithm" is proved only for this class. Whether the bound holds with coding across writes is not settled by
  the paper. (`theorem2`, `corollary2`)
* **Lemma 2's proof is wrong; the lemma is trivially true.** The proof says that choosing adaptively among `m`
  encoders forces `log₂ m` extra bits. It does not: two encoders of a 4-element set into 2 bits, chosen adaptively,
  decode without an extra bit. The lemma itself holds because an adaptive choice of encoders is one fixed function.
  (`lemma2_no_extra_bits`, `lemma2`)
* **Under-specified storage measure.** `C⁺(t)` counts writes whose bits are in base objects *or in other clients*.
  So Observation 1 (storage `≥ |C⁺(t)|`) holds only if the storage counts copies of other writers' data held by
  clients. We use that measure in the hypothesis of Theorem 2. The conclusion of Corollary 2 is about base objects
  only. (`Alg.storage`, `obs1`)
* **Proof gaps in Section 4; all statements hold in the black-box model.**
  - *Lemma 3* ignores copies: a client may read another writer's bits and spread them over several objects. The
    claim holds because `Ad` never lets an RMW touch an object of `F(t)`. A batch of `D` bits is frozen in its
    object the moment it is stored, and smaller batches never add up to `D`. Our invariant states exactly this.
    (`inv_exec`, `lemma3`)
  - *Lemma 4*: iterating the growth of `T_cᵢ` is unnecessary. It suffices to crash `F(t)` itself in the solo run.
    (`solo_progress`, `rule1_infinitely_often`)
  - *Theorem 2*: the fair run `r'` cannot be "identical to `r`", because clients that receive finitely many
    responses must stop taking steps. We remove their later steps and show by simulation that nothing else changes.
    Liveness of each RMW of the other clients uses the oldest-first rule of `Ad`. (`theorem2_run`)
  - The bound needs at least `S + 1` clients (`S` concurrent writers and a reader); the paper only says Π is
    finite. (`theorem2`)
* **Theorem 3 / Corollary 4 are misstated (not formalized).** "With at most `c < k` concurrent writes the storage is
  bounded by `(c + 1)D/k` bits" is false as written: the initial configuration already stores
  `(2f + k)D/k` bits. Lemma 12 has the intended `(2f + k)(c + 1)D/k`, and it assumes `c < k − 1`.
* **Typos.** Lemma 12's proof cites itself (meant Lemma 11) and writes `ts' ≥ ts₁ > ts₁`. Corollary 5 says
  "WF-termination" for FW-termination. In Observation 2's proof, `|B| = N − f` should be `n − f`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous fault-prone shared memory (Section 2.1). Deterministic clients `C` (finite) trigger arbitrary
  atomic RMWs on base objects `N`. A triggered RMW stays pending until an `exec` event applies it and delivers the
  response, and a client may have several pending RMWs. Taking effect and responding are one event. This only
  restricts the runs, which makes the hypotheses weaker and the lower bound stronger.
* Crash failures of clients and of at most `f` base objects. Failures are not events: a failure pattern enters the
  fairness predicate `Fair` (crashed clients take finitely many steps, crashed objects execute finitely many RMWs,
  correct clients are scheduled infinitely often, RMWs of correct clients on correct objects eventually take
  effect). Lock-freedom and weak regularity (MWRegWeak) are as in Section 2.2, quantified over all runs and all
  value assignments. No randomness. `f < n/2` is not needed for the lower bound.
* Black-box storage. A write carries no value; write `w` has value `val w` for an arbitrary value assignment. Data
  are blocks `(w, j)` of `sz j ≥ 1` bits with contents `enc j (val w)`, where `enc` is the algorithm's code (e.g.
  erasure-code pieces or full replicas). Blocks only flow: they are stored by RMWs from the client's holdings,
  carried back by responses, and created only by their writer. A read's output depends only on the contents of the
  blocks it holds. `D = ⌈log₂|V|⌉`; `F(t)` = objects holding `D` bits of one write. Storage = bits in base objects
  plus copies held by clients other than the writer.
* Proof structure as in the paper: the adversary `Ad` (Definition 1) runs `S` writes. The information-theoretic step
  (`restore`): a reader that, for every value assignment, returns the value of one of finitely many writes holds
  `D` bits of one of them.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `lemma1` | `Coding.lean` |
| Lemma 2 (and the false step of its proof) | `lemma2`, `lemma2_no_extra_bits` | `Coding.lean` |
| Theorem 1 (false; true cumulative version) | `theorem1_false`, `theorem1_cumulative` | `Coding.lean` |
| "`D` bits are needed to restore a value" | `restore`, `exists_ne_of_bits_lt` | `Coding.lean` |
| Model, fairness, lock-freedom, weak regularity | `Alg`, `Alg.Fair`, `Alg.LockFree`, `Alg.WeakRegular` | `Model.lean` |
| Definition 1 (adversary `Ad`) | `Alg.Ad` | `Adversary.lean` |
| Observation 1 | `Alg.obs1` | `Adversary.lean` |
| Observation 3 | `Alg.full_step_Ad`, `Alg.full_eventually_const` | `Adversary.lean`, `LowerBound.lean` |
| Lemma 3 | `Alg.inv_srun_Ad`, `Alg.lemma3` | `Adversary.lean` |
| Observation 2 | `Alg.reader_restore` | `Solo.lean` |
| Corollary 1 | `Alg.noReturn` | `LowerBound.lean` |
| Lemma 4 | `Alg.solo_progress`, `Alg.rule1_infinitely_often` | `Solo.lean`, `LowerBound.lean` |
| Theorem 2 | `Alg.theorem2` (run of `Ad`: `Alg.theorem2_run`) | `LowerBound.lean` |
| Corollary 2 | `Alg.corollary2` | `LowerBound.lean` |
| Lemma 5 (base objects store ≤ `n` pieces) | `Safe.objBits_le` | `SafeAlgorithm.lean` |
| Lemma 6 (wait-free) | `Safe.waitFree` | `SafeAlgorithm.lean` |
| Lemmas 7–9, Observation 4 (strongly safe; reader takes the largest qualifying timestamp) | `Safe.stronglySafe`, `Safe.ots_step`, `Safe.inter_card` | `SafeAlgorithm.lean` |
| Corollary 3 (+ replication instance) | `Safe.corollary3`, `Safe.corollary3_replication` | `SafeAlgorithm.lean` |
| Algorithm 2 as written is unsafe (`n = 3`, `f = 1`, `k = 1`) | `Safe.not_stronglySafe`, `Safe.not_weakRegular` | `SafeCounterexample.lean` |
| Non-vacuity: a lock-free, weakly regular algorithm (one object, `f = 0`) | `NonVacuity.atomicAlg_lockFree`, `NonVacuity.atomicAlg_weakRegular`, `NonVacuity.theorem2_atomicAlg` | `NonVacuity.lean` |

**Not formalized.** Section 5 (the adaptive strongly regular algorithm, Theorem 3, Lemmas 10–22); Section 3.2
(intuition).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
model is self-contained (Mathlib only). The hypotheses of Theorem 2 are satisfiable: a single-object atomic register
algorithm is lock-free and weakly regular in the model (`NonVacuity.lean`); for `f ≥ 1` no algorithm satisfying them
was formalized. Lean namespace: `Podc.ReliableStorageSpace`.
