# You Can Lie but Not Deny — PODC 2025

Xing Hu, Sam Toueg. *You can lie but not deny: SWMR registers with signature properties in systems with Byzantine
processes.* PODC 2025. DOI [10.1145/3732772.3733550](https://doi.org/10.1145/3732772.3733550). Formalized version:
arXiv [2504.09805](https://arxiv.org/abs/2504.09805) v2; numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** We found no mistake in what we checked, the optimality result of Section 10. For
`3 ≤ n ≤ 3f` there is no correct implementation from SWMR registers of the one-shot test-or-set object
(Theorem 29), nor of verifiable, authenticated and sticky registers (Theorem 31), and Observation 30 (test-or-set
from each of these registers) also holds. The implementations for `n > 3f` (Theorems 14, 20, 25), the other half
of the paper's main point, are not formalized and were not checked.

## Mistakes in the paper

No mistakes in the statements.

### Typos
- Section 6 introduces the authenticated register as "a multivalued SWMR *verifiable* register".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Podc/Computability/Distributed/SharedMemory/Byzantine/Model.lean`, staged for CSLib)
* Asynchronous shared memory with `n = card P` processes, at most `f` of which are Byzantine. Implementations are
  deterministic programs (CSLib `Impl`). Base objects are atomic and come with access rights. Correct processes
  may take steps outside their operation intervals (helping).
* A Byzantine process applies arbitrary primitives it has the right to apply. For SWMR registers this means
  arbitrary writes to its own registers. Correct processes are invoked only when idle, and only with allowed
  operations (e.g. only the setter `Set`s).
* Byzantine linearizability (Definition 7). Some well-formed history `h'` uses only allowed operations, agrees
  with `h` on the correct processes, and is linearizable. Correctness (Definition 9, `Impl.ByzCorrect`): every
  finite execution is Byzantine linearizable, and correct processes complete their operations in every fair
  infinite execution. This holds for every set of `≤ f` Byzantine processes and every invocation pattern allowed
  by `adm` (one-shot for test-or-set, unrestricted for the registers). Requiring Byzantine linearizability only
  for finite executions is implied by the paper's definition, so the impossibility results are at least as
  strong as stated.
* Base objects: any family of single-writer objects (only the owner changes an object, and it can overwrite it
  with any state). This covers SWMR registers of arbitrary value types, any number per process.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 7, 9 | `ByzLinearizable`, `Impl.ByzCorrect` | `Podc/…/Byzantine/Model.lean` |
| Definitions 10, 15, 21, 26 | `verReg`, `authReg`, `stickyReg`, `testOrSet` (+ `…Allowed`) | `Objects.lean` |
| Observation 27, 11–13, 16–18, 22–24 | `tosSig`, `verSig`, `authSig`, `stickySig` (`SigTest` structures) | `Objects.lean` |
| Lemma 28 (generalized) | `SigTest.validity`, `SigTest.unforgeability`, `SigTest.relay` | `SigTest.lean` |
| Theorem 29 (generalized core) | `SigTest.no_byzCorrect` | `Impossibility.lean` |
| Theorem 29 | `theorem29` | `Main.lean` |
| Observation 30 | `observation30`, `observation30_verifiable`, `observation30_authenticated`, `observation30_sticky` | `Observation30.lean` |
| Theorem 31 | `theorem31_verifiable`, `theorem31_authenticated`, `theorem31_sticky` | `Main.lean` |
| (degenerate case) | `authenticated_unit_byzCorrect`, `authenticated_unit_swmr` | `Degenerate.lean` |

The impossibility proof (histories H1–H3 of Figure 1) is sound. Lemma 28 has only a proof sketch in the paper; the
sketch is correct, and we prove the lemma in full (`SigTest.validity`, `SigTest.unforgeability`, `SigTest.relay`).

**Degenerate value domains (implicit convention).** Theorem 31 for authenticated registers is false if the value
domain is `{v₀}`: then `Read` always returns `v₀` and `Verify(v₀)` always returns true, so every operation can
return immediately. The sticky register is likewise trivial for an empty domain. The paper speaks of
*multivalued* registers throughout, which excludes these cases, so this is an implicit convention rather than an
error. We make it explicit with the hypotheses `v ≠ v₀` and `Nonempty V`.
(`authenticated_unit_swmr`, `theorem31_authenticated`)

**CSLib candidates.** `Podc/Computability/Distributed/SharedMemory/Byzantine/Model.lean` and `Restrict.lean`
(Byzantine shared-memory model, Byzantine linearizability, replay, single-writer objects, termination ⇒ completion,
history restriction); the positional linearization lemmas `stAt`, `idx`, `lin_*` of `SigTest.lean`.

**Not formalized.**
* The implementations for `n > 3f` (Algorithms 1–3, Theorems 14, 20, 25 and their appendix proofs).
* The remark that `n = 2` is trivial.
* The paper's derivation of Theorem 31 from Theorem 29 and Observation 30, which we did not check. It goes through
  an unstated composition property: a correct implementation of test-or-set *from a verifiable register*, composed
  with a correct implementation of the verifiable register *from SWMR registers*, gives a correct implementation
  of test-or-set *from SWMR registers*. The paper's Section 3.2 motivates Byzantine linearizability by exactly this
  use ("as if it were an atomic object"), so the step is a standard tacit assumption. For deterministic
  implementations it is plausible, but it is not trivial: Byzantine processes may deviate at both levels. We avoid
  the composition and prove Theorem 31 directly for all four objects at once (`SigTest.no_byzCorrect`,
  `theorem31_verifiable`, `theorem31_authenticated`, `theorem31_sticky`). The proof of Theorem 29 only uses three
  properties of a positive test: validity, unforgeability and relay (Lemma 28). We prove these for every
  "signature-like" object directly from Byzantine linearizability, so the impossibility applies to all four objects.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Impl.ByzCorrect` is satisfiable. Observation 30 gives correct implementations for every `f`, and
`authenticated_unit_swmr` gives one from SWMR registers for `3 ≤ n ≤ 3f`. So the impossibility results do not follow from an
unsatisfiable correctness notion. Histories and linearizations come from CSLib `SharedMemory` (`History`,
`LinPoints`). The Byzantine execution model, replay/indistinguishability lemmas and history restriction
(`Podc/Computability/Distributed/SharedMemory/Byzantine/{Model,Restrict}.lean`) are CSLib candidates.
