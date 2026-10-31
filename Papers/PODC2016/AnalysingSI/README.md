# Analysing Snapshot Isolation — PODC 2016

Andrea Cerone, Alexey Gotsman. *Analysing Snapshot Isolation.* PODC 2016. DOI
[10.1145/2933057.2933096](https://doi.org/10.1145/2933057.2933096). Formalized version: the extended version
with the appendix proofs (§A, §B; no arXiv version); numbering follows it. The JACM 2018 version was consulted.

**Verdict: ⚠️ Minor statement issues.** The main results hold as stated: the dependency-graph characterisation of
SI (Theorems 9 and 10, with Lemmas 12, 13, 15), the dynamic chopping criterion (Theorem 16, with Lemmas 17, 24,
26, 27) and its static version (Corollary 18), and the robustness criteria (Theorems 19, 22). The only
statement-level problem is a typo: Definition 20 defines `HistPSI` from `ExecSI` instead of `ExecPSI`, which makes
Theorem 21 false as written.

## Mistakes in the paper

- **Definition 20 typo makes Theorem 21 false as written.** `HistPSI` is defined as
  `{H | ∃VIS, CO. (H, VIS, CO) ∈ ExecSI}`, with `ExecSI` rather than the `ExecPSI` defined on the line above. The
  JACM version has the same typo. Read literally, `HistPSI = HistSI`, and Theorem 21 would then say that SI
  histories are exactly the histories of graphs in `GraphPSI`. That is false: the long-fork history of
  Figure 2(c) has a graph in `GraphPSI` but is not in `HistSI`. The intended definition is evident, and with
  `ExecPSI` Theorem 21 holds (we prove it although the paper cites it).
  (`Examples.theorem21_literal_false`; `theorem21`)
- **Lemma 26, transitivity of `WW_splice(G)`: a missing case.** The proof first shows `T' —WW→ S''` and only then
  `T ≉ S`. In the first part it rules out `S'' —WW→ T'` with a cycle of `DCG(G)` (Figure 10(f)). That cycle is in
  `DCG(G)` only if `S'' ≉ T'`, and the case `T ≈ S` is not treated there. Proving the second part first (it does
  not depend on the first) closes the gap. Routine; the statement is true. (`Chopped.Hyp.splice_ww_trans`)
- **Small slips.** Some derived anti-dependencies `S' —RW→ V'` in the proofs of Lemmas 26 and 27 need
  `S' ≠ V'`; the excluded case is a short cycle forbidden by `G ∈ GraphSI`. §6.1 refers to "the long fork
  anomaly in Figure 4" (it is Figure 2(c)). The proof of Theorem 10(i) says "Figure 3" for Figure 4.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Purely combinatorial and declarative: no processes, failures, timing or randomness. Everything is
finite-relational, and finiteness is never needed.
- Transactions are lists of `read(x,n)`/`write(x,n)` operations in program order, with values in an arbitrary
  type. `T ⊢ read(x,n)`, `T ⊢ write(x,n)` and INT are as in §2. A history `(𝒯, SO)` has an arbitrary `SO` in
  §§2–4 and §6; all results there hold for every `SO`, which is more general than the paper's union of total
  orders.
- Abstract executions `(𝒯, SO, VIS, CO)` and pre-executions use the axioms of Figure 1 and the sets `ExecSI`,
  `ExecSER`, `ExecPSI`, `HistSI`, `HistSER`, `HistPSI`. `max_CO` is a predicate, and its definedness is part of
  EXT.
- Dependency graphs follow Definition 6, with `RW` derived from `WR` and `WW`; `graph(X)` follows Definition 5.
  Cycles are closed walks that may repeat vertices. Edge adjacency is cyclic, so the last and first edges also
  count as adjacent.
- Chopping (§5): a history is given by its sessions, i.e. lists of transactions in session order. `splice(H)`
  concatenates each session into one transaction and has empty `SO`. `DCG(G)`, critical cycles and `splice(G)`
  follow §5 and equation (2).
- Programs for Corollary 18 are abstracted by their numbers of pieces and the pieces' read/write sets. "Produced
  by `P`" means an injective session-to-program map in which the `j`-th transaction matches the `j`-th piece.

**Main results in Lean** (namespace `Podc.AnalysingSI`).

| Paper | Lean | File |
|---|---|---|
| Lemma 15 (least solution of Figure 3) | `lemma15`, `isSolution_sol`, `sol_le` | `Relations.lean` |
| Proposition 7 / 23 | `Execution.prop7`, `Execution.isDepGraph_graph` | `Characterisation.lean` |
| Proposition 14 | `Execution.prop14` | `Characterisation.lean` |
| Lemma 12 | `Execution.lemma12` | `Characterisation.lean` |
| Lemma 13 | `DepGraph.lemma13` | `Characterisation.lean` |
| Theorem 10 (i) soundness, (ii) completeness | `theorem10_soundness`, `theorem10_completeness`, `theorem10` | `Characterisation.lean` |
| Theorem 9 (`HistSI` via `GraphSI`) | `theorem9` | `Characterisation.lean` |
| Theorem 8 (Adya, cited) | `theorem8`, `theorem8_soundness` | `Characterisation.lean` |
| Theorem 21 (parallel SI, cited; `ExecPSI` in Def. 20) | `theorem21`, `theorem21_soundness` | `Characterisation.lean` |
| Theorem 19 | `DepGraph.theorem19` | `Robustness.lean` |
| Theorem 22 | `DepGraph.theorem22` | `Robustness.lean` |
| Lemma 24 | `lemma24` | `Cycles.lean` |
| Proposition 25 | `Txn.reads_flatten_iff`, `Txn.writes_flatten_iff` | `TxnLemmas.lean` |
| Lemma 26 | `Chopped.Hyp.lemma26` | `SpliceLemmas.lean` |
| Lemma 27 | `Chopped.Hyp.lemma27` | `SpliceLemmas.lean` |
| Lemma 17 | `Chopped.Hyp.lemma17` | `SpliceLemmas.lean` |
| Theorem 16 (and `splice(G) ∈ GraphSI`) | `Chopped.theorem16`, `Chopped.theorem16_splice` | `Theorem16.lean` |
| Corollary 18 | `corollary18` | `Corollary18.lean` |
| Fig. 2(d) write skew: `G₃ ∈ GraphSI \ GraphSER`, history in `HistSI \ HistSER` | `Examples.writeSkewGraph_si_not_ser`, `Examples.writeSkew_si_not_ser` | `Examples.lean` |
| Fig. 2(c) long fork: in `HistPSI \ HistSI`; Definition 20 read literally breaks Theorem 21 | `Examples.longFork_psi_not_si`, `Examples.theorem21_literal_false` | `Examples.lean` |
| Fig. 2(b) lost update: `G₅ ∉ GraphPSI`, history not in `HistPSI` | `Examples.lostUpdateGraph_not_isPSI`, `Examples.lostUpdate_not_mem_histPSI` | `Examples.lean` |

**Not formalized.** The equivalence of the axiomatic SI specification with the operational SI concurrency
control, which the paper cites. Also not formalized: §B, i.e. the chopping criteria for serializability and
parallel SI (Theorems 29 and 31, cited) and their comparison with Corollary 18, and most worked examples
(Figures 4–6, 11–13).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
hypotheses are non-vacuous: `Examples.lean` contains concrete dependency graphs, including write skew in
`GraphSI \ GraphSER`. The model is self-contained in this folder: `Model.lean` and `Relations.lean` with Mathlib
only. The Crooks et al. model of `Papers/PODC2017/SeeingIsBelieving/` (`Model.lean`, `Adya.lean`) overlaps:
it also has transactions as operation lists and Adya's `WR`/`WW`/`RW` with SER/SI/PSI conditions, but uses unique
values (a read returns its writer's id), no sessions, and a per-key version order in place of `WW(x)`. A bridge
(SiB histories as `History` with `SO = ∅` and values `Option ι`, version order ↦ `WW`) would let the SI/PSI
characterisations of the two papers be compared (theirs go through Adya's timestamp-based PL-SI); it does not exist
yet. CSLib
candidates: the relational helpers in `Relations.lean` (`exists_strictTotal_extension`, `Acyclic`) and the
labelled-walk library `CycleDefs.lean`/`Cycles.lean`.
