# Linearizability: A Typo — PODC 2021

Gal Sela, Maurice Herlihy, Erez Petrank. *Brief Announcement: Linearizability: A Typo.* PODC 2021, pp. 561–564.
DOI [10.1145/3465084.3467944](https://doi.org/10.1145/3465084.3467944). Formalized version: full version
arXiv:2105.06737v2 (numbering follows it).

**Verdict: ✅ Correct.** Every formalized claim holds as stated:
- Under the original Herlihy–Wing definition (2.2), linearizability is neither local nor nonblocking.
- The amended definition (4.1) is both (Theorems 5.1, 5.2).
- Linearization points are equivalent to 4.1 (Claim 1) but not to 2.2.
- The inclusions of Figure 6 hold, and they are strict.

## Mistakes in the paper

We found no mistakes. Two implicit assumptions are made explicit:
- The "only if" direction of locality (Theorem 5.1) needs the empty history to be legal for every object. This
  follows from the paper's prefix-closed, non-empty specifications.
- "Total operation" (Section 3.3, Theorem 5.2) is read relative to the sequential specification: from every legal
  complete sequential history, some response makes the operation legal.

We did not formalize the paper's own proof of Theorem 5.1 (the Herlihy–Wing minimal-cycle argument). The theorem is
proved by a different route; see below.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Purely combinatorial, Herlihy–Wing style, with no implementations.
- A history is a finite list of events `inv p x o` / `res p x r` over several objects. Well-formedness, `H|p`,
  `H|x`, extensions and `complete(H)` follow the paper.
- Operations are identified explicitly as `(process, object, index)`. The paper identifies operations of `H`,
  `H'`, `complete(H')` and `S` only implicitly, through equivalence.
- Sequential specifications are arbitrary per-object sets of histories. They may be nondeterministic or partial,
  and are not required to be prefix-closed; `hnil` is assumed only where needed.
- Definitions 2.2, 4.1 and 7.1 are stated literally (`LinearizableHW`, `Linearizable`, `LinearizableLP`). In 7.1,
  linearization points are gaps between events, which is equivalent to distinct real-valued points.
- The Section 3 counterexamples use concrete instances: 0/1 register values and queue values 1, 2.

**Proof of Theorem 5.1 (locality).** Instead of the paper's minimal-cycle argument:
- Give each object's operations the running-maximum linearization points from Claim 1.
- Points of different objects never coincide.
- Merge all objects' operations by point. The result respects the real-time order of `H`.

**Main results in Lean** (namespace `Podc2021.LinearizabilityTypo`; general theory in `Cslib.SharedMemory.HerlihyWing`).

| Paper | Lean | File |
|---|---|---|
| Def. 2.2 / 4.1 / 7.1 | `LinearizableHW`, `Linearizable`, `LinearizableLP` | CSLib `HerlihyWing/Defs.lean` |
| §3.1, §5.1: Fig. 1–2 histories linearizable by 2.2, not by 4.1 | `H1_linearizableHW`, `H1_not_linearizable`, `H2_linearizableHW`, `H2_not_linearizable` | `Examples.lean` |
| §3.2: original definition not local (Fig. 3) | `sec3_2_not_local` | `Main.lean` |
| §3.3: original definition not nonblocking | `sec3_3_not_nonblocking` | `Main.lean` |
| **Theorem 5.1** (amended definition is local) | `theorem5_1` | `Main.lean` |
| **Theorem 5.2** (amended definition is nonblocking) | `theorem5_2` | `Main.lean` |
| **Claim 1** (Def. 7.1 ⟺ Def. 4.1) | `claim_1` | `Main.lean` |
| §7: Def. 7.1 not equivalent to Def. 2.2 | `sec7_not_equiv_original` | `Main.lean` |
| §8: 4.1 ⊊ 2.2 | `sec8_amended_lt_original` | `Main.lean` |
| §6, §8: alternative reading (Def. 6.1 + original L2) ⊊ 4.1, Fig. 5 | `sec6_alternative_too_strong`, `Sec6.Hs_not_linearizableAlt` | `Main.lean`, `Alternative.lean` |

**Side result.** CSLib's linearizability notion `Cslib.SharedMemory.IsLinearization` is exactly the amended
Definition 4.1. This is proved as `Cslib.SharedMemory.HerlihyWing.cslib_linearizable_iff` and
`linearizable_iff_cslib`, and `cslib_rejects_H1` shows it rejects Figure 1's history. Other formalizations built on
CSLib (e.g. PODC 2024 *History-Independent Objects*) therefore use the right notion.

**Not formalized.** The non-volatile-memory motivation, the comparison with Lynch's atomicity, and the paper's
minimal-cycle proof of Theorem 5.1.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The definitions are non-vacuous: each is witnessed by explicit linearizable and non-linearizable histories. The
history framework is in CSLib, `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/`.
