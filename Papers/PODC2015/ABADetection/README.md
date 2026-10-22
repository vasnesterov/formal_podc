# ABA Prevention and Detection — PODC 2015

Zahra Aghazadeh, Philipp Woelfel. *On the Time and Space Complexity of ABA Prevention and Detection.*
PODC 2015. DOI [10.1145/2767386.2767403](https://doi.org/10.1145/2767386.2767403). Formalized version:
arXiv [1507.02722](https://arxiv.org/abs/1507.02722) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All lower bounds hold for linearizable implementations:
Theorem 1(a) `m ≥ n − 1` for bounded registers, Theorem 1(b) `t·m ≥ n − 1`, Theorem 1(c)
`2t·m ≥ n − 1`, and Corollary 1 for LL/SC. The paper's own weak correctness condition for
`WeakRead()/WeakWrite()` is mis-stated: even atomic registers violate it. The proof of Lemma 2 also
misses a case. Both are repaired. **Theorem 1(a) is proved only in a weaker form**: for
deterministic obstruction-free implementations. The paper proves it for the strictly larger class of
nondeterministic (e.g. randomized) implementations with nondeterministic solo-termination; that
version is not formalized.

## Mistakes in the paper

* **The WeakRead()/WeakWrite() condition is not implied by linearizability.** Section 2 requires that
  "a WeakRead() `r` by `p` returns True iff there is a WeakWrite() `w` that happens before `r` and
  every other WeakRead() by `p` happens before `w`". It then claims that linearizable ABA-detecting
  registers satisfy this. Read literally, this fails twice.
  First, take a DRead() concurrent with a DWrite(). If it is linearized after the write it returns
  True, but no write *happens before* it.
  Second, take the sequential history `DWrite(); DRead() → True; DRead() → False`. "Every other
  WeakRead() by `p`" includes the *later* read, which does not happen before the write, so the first
  read would have to return False.
  Both histories are executions of the trivial atomic implementation, which is linearizable and
  wait-free. Read literally, the condition cannot be met by any implementation in which a reader
  can complete two reads after a write: in `DWrite(); DRead()` the read must return True, and in
  the extension `DWrite(); DRead(); DRead()` the same read must return False (informal argument, not
  formalized). So lower bounds "for the literal condition" are vacuous. The appendix proof of
  Observation 1 shows the intended meaning ("every *earlier* WeakRead() by `p`", reads not
  concurrent with writes). This is an under-specified definition, not a false theorem. The
  lower-bound proofs use the condition only through Observation 1, and only in situations that
  linearizability does determine. We drop the condition and prove Observation 1 (and Observation 2
  for LL/SC) directly from linearizability. The paper's remark that the lower bounds hold for weaker
  correctness conditions is not covered as such. The abstract theorems (`card_le_of_separates`,
  `..._wcas`, `..._regOrCas`) do apply to any implementation of any object for which clean and dirty
  configurations are distinguishable, i.e. to any repaired weak condition that implies
  Observation 1; no such condition is formalized.
  (`weakSpecLiteral_not_of_linearizable_concurrent`, `weakSpecLiteral_not_of_linearizable_later_read`;
  repaired: `separates_aba`, `separates_llsc`)
* **Lemma 2, Case 1 misses a case (proof gap, statement true).** `q` is poised to read or CAS an
  object `V`, and the proof takes "the first process `z ∈ P` that executes a step on `V` in
  `Exec(C,β)`". No such process need exist. If `q`'s CAS would then succeed, no two-step schedule
  `λ` hides it. The fix is simple. If `q`'s step does not change `V`, it is hidden anyway. If it is a
  successful CAS, case (c) holds directly with `σ = β`, because no process of `P` covers `V`.
  (`lemma2`)
* **Smaller slips in Lemmas 2–3.**
  * Lemma 2 derives `|WCov(C′,R) ∩ P′| ≤ t′` and then only `≤ t`, where `< t′` and `< t` are needed
    and follow from the induction hypothesis.
  * Lemma 2 does not state that `σ` is `(P ∪ {q})`-only and invocation-free, but Lemma 3 uses both.
  * The w.l.o.g. "no `CAS(x,x)`" is unnecessary: such a step can be treated as a read.
  * Lemma 3 has index typos in `λ′` and in `Dⱼ′ = Conf(Dᵢ′, λ′αⱼβⱼ)`, which should end in `βᵢ`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared-memory model: `n` processes (`Fintype P`), atomic base objects, and
  executions as label lists `inv`/`tau`/`ret`. The adversary is an arbitrary scheduler; there are no
  crashes beyond processes stopping.
* **Processes are deterministic.** For Theorem 1(b),(c) and Corollary 1 this is the paper's setting.
  For Theorem 1(a) (and Observation 1) the paper allows nondeterministic implementations with
  *nondeterministic solo-termination*. We assume determinism and obstruction-freedom, which is the
  same progress condition for deterministic implementations. **Our Theorem 1(a) is therefore weaker
  than the paper's**: a space lower bound for a smaller class of implementations, excluding
  randomized ones. The paper's proof looks like it carries over (schedules would carry the coin
  flips), but CSLib's model has no nondeterminism, and this is not checked.
* Implemented objects: the ABA-detecting register `abaObj` (DRead carries the reader) and CSLib's
  LL/SC object `llscObj`. Single-writer use is expressed by the hypotheses that the writer `w0` may
  invoke `DWrite(x)` and each reader `p` may invoke `DRead()`. Executions in the proofs use only
  these operations; the implementation may allow more. Correctness is linearizability.
* Base objects:
  * bounded registers `register (V i)` with `Finite (V i)` (Theorem 1(a));
  * bounded writable CAS objects `wcasObj V` with `Finite V`, where `Read`/`CAS` return the old value
    (Theorem 1(c), Corollary 1(b));
  * for "registers and CAS objects" (Theorem 1(b), Corollary 1(a)), writable CAS objects whose
    `Write`/`CAS` usage is restricted per object (`RegOrCas`).
* Step complexity `≤ t` (`StepBound`): every operation, complete or not, performs at most `t`
  base-object accesses in every execution. Wait-freedom is assumed as in the paper.
* The proofs are generic. The only property of the implemented object they use is `Separates`: clean
  and dirty configurations are distinguishable by the reader (Observations 1/2). It is stated for a
  writer round `ws` (`[DWrite(x)]`, resp. `[LL(), SC(x)]`) and proved from linearizability for both
  objects.

**Main results in Lean** (namespace `Cslib.SharedMemory.ABADetection`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1(a) | `theorem1a` | `Theorem1.lean` |
| Theorem 1(b) | `theorem1b` | `Theorem1.lean` |
| Theorem 1(c) | `theorem1c` | `Theorem1.lean` |
| Corollary 1(a), (b) | `corollary1a`, `corollary1b` | `Theorem1.lean` |
| Lemma 1 | `lemma1` (and `card_le_of_separates`) | `Lemma1.lean` |
| Lemma 2 | `lemma2` | `Lemma2.lean` |
| Lemma 3 | `lemma3` | `Lemma3.lean` |
| Observation 1 (App. B.1) | `separates_aba` | `Observation.lean` |
| Observation 2 (App. B.3) | `separates_llsc` | `Observation.lean` |
| WeakRead/WeakWrite condition vs. linearizability | `weakSpecLiteral_not_of_linearizable_concurrent`, `weakSpecLiteral_not_of_linearizable_later_read` | `WeakSpec.lean` |
| abstract tradeoffs (any object with `Separates`) | `card_le_of_separates_wcas`, `card_le_of_separates_regOrCas` | `Theorem1.lean` |

Other files: `Defs.lean` defines the objects, `Std`/`Clean`/`Dirty`/`Separates` and `StepBound`.
`Common.lean` has the finishing round `γᵢ` and the clean/dirty bookkeeping. `CasDefs.lean` has
successful schedules (`Succ`), `WCov`/`CCov` and `Budget`.

**Not formalized.** Theorem 1(a) for nondeterministic implementations (the paper's full statement). The upper bounds: Theorem 2 (LL/SC/VL
from one bounded CAS object), Theorem 3 (ABA-detecting register from `n + 1` registers) and
Appendix A.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The model comes from CSLib (`SharedMemory/{Model,History,Covering,Solo,Progress}`,
`Objects/LLSC`). The non-vacuity of `Separates` is shown by `separates_aba`/`separates_llsc`: it
follows from linearizability. There is no non-vacuity witness for the full hypotheses of Theorem 1
(an implementation from bounded objects). The paper's upper bounds would provide one, but they are
not formalized. CSLib candidates: the generic part of `Common.lean` (`exists_round`),
`Succ`/`WCov`/`CCov` with their lemmas in `CasDefs.lean`, and the step-reordering lemma of
`Lemma2.lean`; all are marked in the files.
