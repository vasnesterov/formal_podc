# Seeing is Believing — PODC 2017

Natacha Crooks, Youer Pu, Lorenzo Alvisi, Allen Clement. *Seeing is Believing: A Client-Centric Specification of
Database Isolation.* PODC 2017. DOI [10.1145/3087801.3087802](https://doi.org/10.1145/3087801.3087802).
Formalized version: the 10-page author copy (identical in content to the 11-page UT copy; the appendices and the
technical report TR-17-06 with the deferred proofs were not available).

**Verdict: ✅ Correct.** The state-based characterizations are equivalent to Adya's: serializability ⇔ PL-3
(Theorem 1), snapshot isolation ⇔ PL-SI (Theorem 2), read committed ⇔ PL-2 (Theorem 3), read uncommitted ⇔ PL-1
(Theorem 4) and PSI ⇔ PL-2+ (the dependency-graph half of Theorem 10), once Adya's side is read, as the paper's
proofs do, as "for *some* version order (and some start/commit timestamps)". The proof sketches of Theorems 1 and 2
go through; the missing steps are routine.

## Mistakes in the paper

No mathematical errors were found in the checked statements. Imprecisions an expert should be aware of:

- **What "≡ ¬G1 ∧ ¬G2" quantifies over.** The left-hand sides of Theorems 1–4 and 10 only see the transactions and
  the values they read; Adya's phenomena are properties of a *history*, which also fixes a version order (and, for
  SI, start/commit timestamps). The theorems are true when the history's version order and timestamps are
  existentially quantified — exactly what the ⇒ halves of the proof sketches construct from `e` — and false if they
  refer to a given history: two transactions that blindly write `x` and `y` are serializable, but with the version
  order `x₀ ≪ x₁`, `y₁ ≪ y₀` the history exhibits G0 (so also G1); for that history Theorem 4 would even claim ¬G0
  (`fixed_versionOrder_counterexample`). The paper's remark that its definitions "do not rely on timestamps" and
  Theorem 4 (both sides then trivially true) confirm the existential reading, which we formalize.
- **Proof sketches.** Theorem 1 (⇐) argues only with anti-dependency edges that a version read by `T` is not
  overwritten before `T`; a writer whose version precedes the one read must be excluded via write-dependency edges, and
  aborted reads via ¬G1a. Theorem 2 (⇒) needs NO-CONF (not just completeness) to give write-dependency edges a
  start-dependency; its start points coincide for transactions sharing a snapshot (the paper's time oracle assigns
  distinct timestamps — we perturb them); and for a transaction without operations every state is "complete", including
  states after its parent state, so the chosen snapshot must be capped at the parent state. All routine.
- **Small slips.** Section 3 says states hold values "produced by writes from aborted or committed transactions", but
  executions apply only the transactions of `𝒯`, which must be the committed ones (otherwise Theorem 1 ⇒ fails on
  aborted reads). Phenomenon G1b (intermediate reads) is vacuous under the paper's assumption that a transaction
  writes a key at most once.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (Purely combinatorial; no processes, failures, timing or randomness.)
- Keys `K` and transaction identifiers `ι` are arbitrary types; values are uniquely identifiable: the value written
  by `T` to `k` is `some T`, the initial value `⊥` is `none` (`Model.lean`). A `TxnSet` lists, for every transaction,
  its reads (with the values returned) and writes in program order, and the finite set of committed transactions `𝒯`;
  other transactions are aborted.
- An execution is a permutation of `𝒯`; states `s_0, …, s_n` are indexed by position (`Execution.state`), so a
  read-only transaction yields two equal but distinct states, as in the paper's sequence `𝒮_e`. Read states
  (Definition 2, including the conventions for writes and for reads after an own write), PREREAD, COMPLETE, NO-CONF,
  D-PREC (`▶`), `sf_o`, `sl_o` and the commit tests of Table 1 (SER, SI, RC, RU, PSI) are transcribed literally;
  `TxnSet.Satisfies CT := ∃ e, ∀ T ∈ 𝒯, CT e T` is Definition 5.
- Adya's side (`Adya.lean`): a version order is a strict total order per key on the committed writers; ww/rw edges use
  the *next* version (the first committed version after `x_init` for reads of `⊥`), wr edges reads of committed
  versions, all between distinct transactions; timestamps are distinct with start < commit, `T →sd T'` iff
  `commit T < start T'`. G0, G1 = G1a ∨ G1c, G2, G-single, G-SIa, G-SIb as in Adya's thesis (item reads/writes only).
- Theorems assume `TxnSet.WellFormed`: a value of another transaction that is read was written by it, and a transaction
  reads its own value only after writing it (Adya's well-formedness; without the latter the equivalences fail
  trivially).

**Main results in Lean** (namespace `Podc.SeeingIsBelieving`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (CT_SER ⇔ ¬G1 ∧ ¬G2) | `theorem1` | `Serializability.lean` |
| Theorem 2 (CT_SI ⇔ ¬G1 ∧ ¬G-SI) | `theorem2`; directions `theorem2_of_adya` (timestamps in any linear order), `theorem2_to_adya` | `SnapshotIsolation.lean` |
| Theorem 3 (CT_RC ⇔ ¬G1) | `theorem3` | `ReadCommitted.lean` |
| Theorem 4 (CT_RU ⇔ ¬G0) | `theorem4` | `ReadCommitted.lean` |
| Theorem 10, PL-2+ part (CT_PSI ⇔ ¬G1 ∧ ¬G-single) | `theorem10`; directions `theorem10_to_adya`, `theorem10_of_adya` | `ParallelSI.lean` |
| Table 1 / Figure 4: SER ⇒ SI ⇒ PSI ⇒ RC on the same execution | `satisfies_hierarchy`, `Execution.ctPSI_of_ctSI` | `Hierarchy.lean` |
| Write skew (Fig. 1(r), Fig. 3): SI but not serializable | `writeSkew_SI`, `writeSkew_not_Ser`, `SI_not_imp_Ser` | `Examples.lean` |
| Adya's side needs "∃ version order" | `fixed_versionOrder_counterexample` | `Examples.lean` |

**Not formalized.** Theorems 5–9 and the PSI half of Theorem 10 (they compare with operational or timestamp-based
specifications — Sovran et al.'s PSI, read atomic, Strong SI, ANSI SI/GSI, Strong Session SI/PC-SI — that the paper
does not define formally), strict serializability, the strictness of Figure 4 beyond SER ⊋ SI, Section 5.3.

**Trust.** No `sorry`; all listed theorems use only `propext`, `Classical.choice`, `Quot.sound`. The hypotheses are
non-vacuous: `writeSkew` and `blindWrites` are well-formed instances. Shared code: the topological-sort lemma
`Finset.exists_topologicalSort` (staged in `Podc/Foundations/Order/TopologicalSort.lean`, CSLib candidate); the
transaction/history model (`Model.lean`, `Adya.lean`) is marked as a CSLib candidate.
