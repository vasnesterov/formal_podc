# ABA Prevention and Detection — PODC 2015

Zahra Aghazadeh, Philipp Woelfel. *On the Time and Space Complexity of ABA Prevention and Detection.*
PODC 2015. DOI [10.1145/2767386.2767403](https://doi.org/10.1145/2767386.2767403). Formalized version:
arXiv [1507.02722](https://arxiv.org/abs/1507.02722) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The lower bounds hold for linearizable implementations: Theorem 1(a) `m ≥ n − 1` for bounded
registers (checked for deterministic implementations only), Theorem 1(b) `t·m ≥ n − 1`, Theorem 1(c) `2t·m ≥ n − 1`, and
Corollary 1 for LL/SC. The repairs are local: the WeakRead()/WeakWrite() condition is reworded and the proof of Lemma 2
gets one more case. The upper bounds of Theorems 2 and 3 were not checked.

## Mistakes in the paper

### 🔧 Section 2 (the WeakRead()/WeakWrite() correctness condition)
The paper claims that linearizable ABA-detecting registers satisfy its WeakRead()/WeakWrite() condition, but read literally even the trivial atomic implementation violates it (`weakSpecLiteral_not_of_linearizable_concurrent`, `weakSpecLiteral_not_of_linearizable_later_read`).

**Impact.** An under-specified definition, not a false theorem: the lower-bound proofs use the condition only through Observation 1, which we prove directly from linearizability (`separates_aba`, `separates_llsc`), so all lower bounds hold for linearizable implementations.

**Details.** Section 2 requires that "a WeakRead() `r` by `p` returns True iff there is a WeakWrite()
`w` that happens before `r` and every other WeakRead() by `p` happens before `w`". Read literally,
this fails twice.
- Take a DRead() concurrent with a DWrite(). If it is linearized after the write it returns True,
  but no write *happens before* it.
- Take the sequential history `DWrite(); DRead() → True; DRead() → False`. "Every other WeakRead()
  by `p`" includes the *later* read, which does not happen before the write, so the first read
  would have to return False.

Both histories are executions of the trivial atomic implementation, which is linearizable and
wait-free. Read literally, the condition cannot be met by any implementation in which a reader can
complete two reads after a write: in `DWrite(); DRead()` the read must return True, and in the
extension `DWrite(); DRead(); DRead()` the same read must return False (informal argument, not
formalized). So lower bounds "for the literal condition" are vacuous. The appendix proof of
Observation 1 shows the intended meaning ("every *earlier* WeakRead() by `p`", reads not concurrent
with writes), and the proofs use the condition only in situations that linearizability does
determine.

**Repair.** We drop the condition and prove Observation 1 (and Observation 2 for LL/SC) directly
from linearizability (`separates_aba`, `separates_llsc`). The abstract theorems
(`card_le_of_separates`, `..._wcas`, `..._regOrCas`) apply to any implementation of any object for
which clean and dirty configurations are distinguishable, i.e. to any repaired weak condition that
implies Observation 1; no such condition is formalized.

### ✏️ Slips
- Lemma 2 derives `|WCov(C′,R) ∩ P′| ≤ t′` and then only `≤ t`, where `< t′` and `< t` are needed
  and follow from the induction hypothesis.
- Lemma 2 does not state that `σ` is `(P ∪ {q})`-only and invocation-free, but Lemma 3 uses both.
- Lemma 3 has index typos: `λ′` repeats `αᵢ₊₁` where `αᵢ₊₂` is meant, and `Dⱼ′ = Conf(Dᵢ′, λ′αⱼβⱼ)` should end in `βᵢ`.

## Proof gaps (statements true)

### 🔧 Lemma 2, Case 1 (the "first process `z ∈ P`" on `V`)
The proof takes "the first process `z ∈ P` that executes a step on `V` in `Exec(C,β)`", but no such process need exist.

**Impact.** The lemma stands; repaired with a simple extra case (`lemma2`).

**Details.** Here `q` is poised to read or CAS an object `V`. If no process of `P` accesses `V` and
`q`'s CAS would succeed, no two-step schedule `λ` hides it.

**Repair.** If `q`'s step does not change `V`, it is hidden anyway. If it is a successful CAS,
case (c) holds directly with `σ = β`, because no process of `P` covers `V`. (`lemma2`)

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
* The paper's w.l.o.g. "no `CAS(x,x)`" is unnecessary: such a step can be treated as a read.
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

**Not formalized.** Theorem 1(a) and Observation 1 for nondeterministic implementations with nondeterministic
solo-termination (the paper's full statement, a strictly larger class). The paper's remark that the lower bounds also
hold for the weak condition itself: no repaired condition is formalized. The upper bounds: Theorem 2 (LL/SC/VL
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
