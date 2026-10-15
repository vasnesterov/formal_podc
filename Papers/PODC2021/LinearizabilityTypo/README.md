# Linearizability: A Typo (PODC 2021)

Gal Sela, Maurice Herlihy, Erez Petrank. *Brief Announcement: Linearizability: A Typo.*
PODC 2021, pp. 561–564, DOI 10.1145/3465084.3467944.
- Formalized version: the full version **arXiv:2105.06737v2** (29 Jul 2021). Local copy:
  `papers/2021/3465084.3467944_Brief_Announcement_Linearizability_A_Typo.pdf`.
- Numbering below follows the arXiv version.

## Status

**Complete. No `sorry`, no axioms.** `lean_verify` on every theorem in `Main.lean` reports only
`propext`, `Classical.choice` and `Quot.sound`. Build with
`lake build Papers.PODC2021.LinearizabilityTypo.Main`.

**The paper is correct.** Every claim we formalized holds:
- Under the original Herlihy–Wing definition (with the typo), linearizability is neither local
  nor nonblocking.
- The amended definition is local (Theorem 5.1) and nonblocking (Theorem 5.2).
- Linearization points are equivalent to the amended definition (Claim 1), but not to the
  original one.
- The inclusions of Figure 6 hold, and they are strict.

The only implicit assumptions we made explicit are:
- The empty history is legal for every object. Theorem 5.1 needs this in its "only if"
  direction; it follows from the paper's "prefix-closed" specifications.
- Totality is relative to the sequential specification.

See `differencies.md`.

**CSLib.** `Cslib.SharedMemory.IsLinearization` implements the **amended** definition
(Definition 4.1), not the flawed original one. Its `realtime` field enforces real-time order
towards pending instances that are linearized. We proved the equivalence exactly:
- `Cslib.SharedMemory.HerlihyWing.cslib_linearizable_iff`: for well-formed executions, `∃ L, IsLinearization α L` ↔
  `Linearizable (specOf A) (toHist α)`.
- `Cslib.SharedMemory.HerlihyWing.linearizable_iff_cslib`: the same for every well-formed single-object history.
- `cslib_rejects_H1`: CSLib's notion rejects Figure 1's `H1`, which Definition 2.2 accepts.

So the CSLib-based formalizations (e.g. History-Independent Objects, PODC 2024) use the right
notion.

## Model (explicit)

This is a purely combinatorial model of histories in the Herlihy–Wing style, with no
implementations.
- **Histories** are finite lists of events `inv p x o` / `res p x r` over several objects
  (`Cslib.SharedMemory.HerlihyWing.History`).
- **Defined notions:**
  - `H|p` (`restrictP`) and `H|x` (`restrictX`);
  - equivalence (`Equiv`);
  - well-formedness (`WellFormed`: every `H|p` is sequential);
  - extensions (`IsExtension`) and `complete(H)` (`complete`);
  - sequential histories (`IsSeq`, `seqHist`);
  - legality w.r.t. a per-object set of sequential histories (`SeqSpec`, `Legal`).
- **Operations** are identified by `OpId` = (process, object, index); see `differencies.md` §2.
- **Real-time order:** `RT H a b` is `a <_H b`. `Precedes` is the split-based version, and
  `tInv`/`tRes` express it as a comparison of event times.
- **Specifications** may be arbitrary (nondeterministic, partial); `detSpec` covers
  deterministic objects. `Total` is the paper's "total operation".

## Main results ↔ Lean

The general theory is in `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/` (namespace `Cslib.SharedMemory.HerlihyWing`). The paper-specific
results are in this folder (namespace `Podc2021.LinearizabilityTypo`).

| Paper | Lean | File |
|---|---|---|
| Def. 2.2 (original, with the typo) | `LinearizableHW` | `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Defs.lean` |
| Def. 4.1 (amended) | `Linearizable` | same |
| Def. 7.1 (linearization points) | `LinearizableLP` | same |
| Def. 6.1 + original L2 (Section 6) | `Sec6.LinearizableAlt` | `Alternative.lean` |
| list characterizations of 2.2 / 4.1 | `linearizableHW_iff`, `linearizable_iff` (`IsLinO`, `IsLinA`) | `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Equiv.lean` |
| §3.1 / §5.1: `H1`, `H2` linearizable by 2.2, not by 4.1 | `H1_linearizableHW`, `H1_not_linearizable`, `H2_linearizableHW`, `H2_not_linearizable` | `Examples.lean` |
| §3.2: original definition not local (Fig. 3) | `sec3_2_not_local` (= `not_local_HW`), `H3_restrictX_linearizableHW`, `H3_not_linearizableHW`, `not_forall_local_HW` | `Main.lean`, `Examples.lean` |
| §3.3: original definition not nonblocking | `sec3_3_not_nonblocking` (= `not_nonblocking_HW`), `not_nonblocking_HW_queue`, `H1_res_not_linearizableHW`, `H2_res_not_linearizableHW`, `not_forall_nonblocking_HW` | `Main.lean`, `Examples.lean` |
| §5.2: object subhistories of Fig. 3 not linearizable by 4.1 | `H3_restrictX_not_linearizable` | `Examples.lean` |
| **Theorem 5.1** (locality, amended) | `theorem5_1` (= `Cslib.SharedMemory.HerlihyWing.locality`; "if" part without assumptions: `linearizable_of_restrictX`) | `Main.lean`, `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Locality.lean` |
| **Theorem 5.2** (nonblocking, amended) | `theorem5_2` (= `Cslib.SharedMemory.HerlihyWing.Linearizable.nonblocking`) | `Main.lean`, `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Nonblocking.lean` |
| **Claim 1** (7.1 ⟺ 4.1) | `claim_1` (= `Cslib.SharedMemory.HerlihyWing.claim1`, list form `linearizableLP_iff`) | `Main.lean`, `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/LinPoints.lean` |
| §7: 7.1 not equivalent to 2.2 | `sec7_not_equiv_original` | `Main.lean` |
| §8: 4.1 ⊊ 2.2 | `sec8_amended_lt_original` (`Cslib.SharedMemory.HerlihyWing.Linearizable.linearizableHW`) | `Main.lean`, `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Equiv.lean` |
| §6 / §8: alternative interpretation ⊊ 4.1 (Fig. 5, `H_s`) | `sec6_alternative_too_strong`, `Sec6.Hs_linearizable`, `Sec6.Hs_not_linearizableAlt` | `Main.lean`, `Alternative.lean` |
| §4 remark: L2 ⟺ `<_{H'} ⊆ <_S` | `WellFormed.precedes_complete_iff` | `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Complete.lean` |
| CSLib's `IsLinearization` = Def. 4.1 | `cslib_linearizable_iff`, `linearizable_iff_cslib`, `isLinearization_iff_isLinA`, `cslib_rejects_H1` | `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/Bridge.lean`, `Main.lean` |

## CSLib candidates

All of `Cslib/Computability/Distributed/SharedMemory/HerlihyWing/` was moved to CSLib. It is a multi-object
Herlihy–Wing history framework that complements `Cslib.SharedMemory`, which has a single object
and no history-level notions such as extensions or `complete`.
- `History`, `Defs`, `Basic`, `WellFormed`, `Times`, `Seq`, `DetSpec`: histories, the three
  definitions, well-formedness and event times.
- `Complete`, `Equiv`: `complete(H)` and the definition ⟺ list characterizations.
- `Locality`, `Nonblocking`, `LinPoints`: Theorems 5.1 and 5.2 and Claim 1. This is the first
  locality/composition theorem in our infrastructure.
- `Bridge`: the bridge to `Cslib.SharedMemory.IsLinearization`.

The generic register/queue run lemmas in `Examples.lean` are candidates too.

## Effort

About 0.8M tokens in total: the paper agent plus 3 subagents (Def ⟺ list equivalences, CSLib
bridge, Section 3 counterexamples).
