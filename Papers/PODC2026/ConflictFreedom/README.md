# Conflict-Freedom as a Progress Condition — PODC 2026

Petr Kuznetsov, Pierre Sutra, Guillermo Toyos-Marfurt. *Conflict-Freedom as a Progress Condition.*
PODC 2026. DOI [10.1145/3796701.3815956](https://doi.org/10.1145/3796701.3815956). Formalized version:
extended version, arXiv [2605.19531](https://arxiv.org/abs/2605.19531) v1; numbering follows it.

**Verdict: 🛠️ Proof repaired.** Every checked result holds as stated:
- the progress hierarchy (Prop. 3.3);
- invariance of return values on traces (Lemmas 4.1–4.2);
- the read-write generalized commit-adopt (Alg. 2, Thm. 5.1);
- the universal construction built from it (Alg. 1), which is linearizable and weakly conflict-free (Thms. 4.3, 4.4).

The appendix proofs of Adoption and Commitment for Algorithm 2 contain false intermediate claims. They also
silently use coherence of the trace order. Invariant (I) in the proof of Theorem 4.4 is stated too broadly. We
give correct proofs.

## Mistakes in the paper

* **Lemma A.3 (Commitment of Algorithm 2): the proof has a false step.** The proof follows a chain
  `i ↦ f(i)` of processes whose candidate was missing. It claims `f(i)` again wrote the least output `β`
  into `B` ("`B_{f(i)} = β`, therefore `f(i) ∈ P_β`"). This fails with three processes, inputs `a`, `ε`, `c`
  over independent letters:
  - `p₁` reads `A = {a, ε}`, writes `(a, True)` and sees only its own entry. It adopts `a`, because the
    input `ε ≤ a` of `p₂` has no `B` entry yet.
  - `p₂` reads `A = {a, ε, c}` later and writes `ac ≠ a`.

  The lemma is still true. We replace the chain by a maximality argument. Among the processes whose input is
  `≤ β₀` (the least candidate) and whose `B`-view contains `β₀`, one with a maximal `B`-view must commit
  (`GCA.commitment_of_reach`).
* **Lemma A.2 (Adoption of Algorithm 2): the proof has a false step.** The case `w_i = True` asserts that no
  flag in `B_i` is `False`. Let `p₁` (input `a`) write `A` and snapshot `{a}` first. A process `p₂` whose later snapshot holds
  `a, b, c` with `b ≍ c` (and `a` independent of both) writes `(a, False)`. Then `p₁` has `w₁ = True` and sees that `False` flag. Adoption still holds,
  because all entries seen by `p₁` equal its input. Our proof is a direct case analysis on the comparability of
  the `A`- and `B`-views (`GCA.adoption_of_reach`).
* **Coherence of the trace order is used but never stated.** Algorithm 2 needs it in two places: in
  "`A_i^co` contains only compatible traces", and in Lemma A.4, to go from incompatible least upper bounds to
  incompatible elements. Both need the fact that a pairwise compatible finite set of traces has an upper
  bound. The paper cites Aalbersberg–Rozenberg only for the existence of GLBs and of LUBs of compatible
  sets. We prove coherence for traces of duplicate-free schedules (`NTrace.compat_of_pairwise`).
* **Theorem 4.4: invariant (I) is claimed for every round `r > r₀`, which the argument does not give.** The
  argument "`u_i` contains only commands from pending operations" fails for operations that complete between
  `τ` and `τ'`. These commit at rounds above `r₀`. The proof only needs (I) at round `r* + 1`, where every
  operation is pending forever, and there it holds: completed operations committed at rounds `≤ r*`, so by
  Lemma A.1 their commands lie in the common prefix (`Alg1.Setup.compat_round`).
* **Proposition 3.4 (not part of the checked results; not formalized): the proof that lock-freedom implies
  weak conflict-freedom is incomplete.** The proof argues that "a suffix where Φ runs pending and alone
  contradicts lock-freedom". It does not, because an idle process is correct and vacuously completes all its
  operations. The fix is to let idle processes invoke and crash. Relatedly, Definition 3.2 (2) as worded is
  satisfied by any process that stays idle. Our Lean definitions are the paper's, verbatim.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Base model.** CSLib's asynchronous shared memory (`Cslib.SharedMemory.Impl`): `n` deterministic
  processes, atomic base objects, any number of crash failures, and an adversarial scheduler with
  arbitrary invocations. There is no randomness.
- **Progress conditions.** They are stated verbatim on CSLib infinite executions (`Progress.lean`).
  - Two operations are concurrent iff they are pending at a common time.
  - A process is correct iff it takes infinitely many steps or is eventually idle.
- **Algorithm 1 as an implementation.** Algorithm 1 is a CSLib implementation of an arbitrary sequential
  object (`Alg1.impl`).
  - Every `GCA_r` is Algorithm 2 on its own two atomic snapshot objects, flattened, since CSLib has no
    composition theorem. The proofs only use the GCA properties of each round (Theorem 5.1 applied to
    the per-round state `gst C r`), as in the paper.
  - The registers `S[j]` are read one by one (a collect).
  - Two ghost variables are used: the per-round GCA history and the commit round of each operation.
- **Domain of the GCA objects.** Mazurkiewicz traces of duplicate-free command schedules (`NTrace`), which
  is all the algorithms ever handle. Algorithm 2 is proved for any `GCADomain`: a meet-semilattice with
  least upper bounds of compatible finite sets that is coherent.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 3.1, 3.2 (conflict-freedom, weak) | `ConflictFree`, `WeakConflictFree` | `Progress.lean` |
| Prop. 3.3 | `progress_hierarchy` | `Progress.lean` |
| Prop. 3.4 (both conflict-freedom equivalences; weak CF ⇔ OF for total `≍`; weak CF ⇒ lock-freedom for empty `≍`) | `conflictFree_iff_of_total`, `weakConflictFree_iff_of_total`, `conflictFree_iff_of_empty`, `WeakConflictFree.lockFreeP_of_empty` | `Progress.lean` |
| Lemma 4.1 | `lemma_4_1` (general: `respOcc_eq_of_traceEquiv`) | `ReturnValues.lean`, `Podc/.../Mazurkiewicz/Equiv.lean` |
| Lemma 4.2 | `lemma_4_2` | `ReturnValues.lean` |
| Trace lattice (Sect. 4.1) + coherence | `NTrace` (`isLUB_lub`, `compat_of_pairwise`, `SemilatticeInf`) | `Podc/.../Mazurkiewicz/NTrace.lean` |
| Thm. 5.1 (Alg. 2 implements GCA) | `GCA.isGCA_of_reach`, `GCA.wait_free` | `GCAProof.lean` |
| Lemma A.1 | `Alg1.lemma_A1'` | `Alg1Inv2.lean` |
| Thm. 4.3 (Alg. 1 linearizable) | `Alg1.linearizable` | `Alg1Lin.lean` |
| Thm. 4.4 (Alg. 1 weakly conflict-free) | `Alg1.weakConflictFree` | `Alg1WCF.lean` |

**Not formalized.**
- The converse lock-freedom ⇒ weak conflict-freedom in Proposition 3.4.
- Section 6: Algorithm 3, Lemmas 6.1–6.2, Theorems 6.4 and 6.6.

**Trust.** There is no `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
- **Non-vacuity.** `Example.lean` instantiates Theorems 4.3–4.4 for the shared counter of Figure 1. Reads
  conflict with updates, and updates commute.
- **Model checking.** A model checker of Algorithm 2 (2–4 processes, traces over 3 letters) found no
  violation.
- **Model origin.** The model comes from CSLib's `Cslib/Computability/Distributed/SharedMemory/`
  (`Model`, `Progress`, `History`).
- **CSLib candidates.** The Mazurkiewicz-trace library (`Podc/Foundations/Data/Mazurkiewicz/`) and the
  progress definitions of `Progress.lean`.
