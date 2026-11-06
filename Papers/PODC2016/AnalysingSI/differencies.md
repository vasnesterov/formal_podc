# Differences between the formalization and the paper

Paper: A. Cerone, A. Gotsman, *Analysing Snapshot Isolation*, PODC 2016, extended version with the appendix
proofs (§A, §B). Numbering follows the PODC/extended version (the JACM 2018 version renumbers: Theorem 10 → 4.2,
Theorem 16 → 5.2, …). The JACM version was consulted; it has the same definitions, proofs and the same slips.

## Statement-level issues

1. **Definition 20 / Theorem 21 (typo, ✏️).** Definition 20 defines
   `HistPSI = {H | ∃VIS, CO. (H, VIS, CO) ∈ ExecSI}` — with `ExecSI`, not the `ExecPSI` defined on the line above
   (checked on the rendered page, p. 9 of the extended version; the JACM version, Definition 5.14, has the same
   typo). Read literally, `HistPSI = HistSI`, and Theorem 21 (`HistPSI` = histories of graphs in `GraphPSI`) is
   false: the long-fork history of Figure 2(c) has a dependency graph in `GraphPSI` but is not in `HistSI`
   (see `Examples.lean`). The intent is evident (the text, the name, Theorem 22 and the proof of Theorem 21 all use
   `ExecPSI`), so we define `HistPSI` with `ExecPSI` and prove Theorem 21 for it (`theorem21`). Theorem 21 is cited from the authors' DISC 2015 paper, but it is a
   numbered theorem of this paper and is used for Theorem 22's interpretation.

## Proof-level issues (statements true)

2. **Lemma 26, transitivity of `WW_splice(G)`: missing case (🔧).** The proof first shows `T' —WW→ S''` and only then
   `T ≉ S`. In the first part, case `V'' —WW→ V'`, it excludes `S'' —WW→ T'` by the cycle
   `T' —WW→ V' —SO⁻¹→ V'' —WW→ S'' —WW→ T'` of Figure 10(f), which is a cycle of `DCG(G)` only if `S'' ≉ T'`; the
   case `S'' ≈ T'` (i.e. `T ≈ S`) is not covered. Repair (used in Lean): prove `T ≉ S` first — the paper's own
   second part does not use the first — after which the cycle is in `DCG(G)`.
3. **Lemmas 26 and 27: implicit distinctness (✏️).** Several anti-dependencies `S' —RW→ V'` are derived without checking
   `S' ≠ V'` (required by Definition 5), e.g. Figure 10(d). When `S' = V'` the configuration is itself a cycle
   `S'' —SO→ S' —WR→ S''` excluded by `G ∈ GraphSI`; the Lean proof handles these cases (`Hyp.no_ww_of_wr_wr`).
4. **Theorem 10(i), construction of the total commit order.** The paper adds unrelated pairs one at a time and
   re-solves the system (Lemma 15 with `R = Rᵢ`). We take one linear extension `L` of the least solution `CO₀`
   (Szpilrajn, `exists_strictTotal_extension`) and apply Lemma 15 with `R = L`; this is the limit of the paper's
   iteration and needs no finiteness. Same idea, shorter proof.
5. **Lemma 13** assumes `VIS` and `CO` acyclic; we only assume `CO` acyclic (`VIS ⊆ CO` by (S3)).
6. **Lemma 24** is stated in the paper for "no two adjacent anti-dependency edges". Our `lemma24` is generic in
   the adjacency predicate `P` and needs `P a b → P c d → P a d` (true for "both are `RW`"); for arbitrary `P` the
   generic statement is false (a figure-eight walk), which does not affect the paper.

## Modelling choices

7. **Transactions** (Definition 1) are lists of operations in program order (`Txn = List (Op Obj V)`); events are
   list positions, so events of different transactions are disjoint by construction. Values range over an
   arbitrary type `V` (the paper: `ℤ`). Transactions are not required to be nonempty (all results hold without it).
8. **Histories** (Definition 2) for §§2–4 and §6 have an arbitrary session-order relation `SO`; Theorems 8, 9, 10,
   19, 21, 22 hold for every `SO` (the paper requires a union of total orders on disjoint sets). For §5 (chopping)
   a history is given by its sessions (`Chopped`: `sess s` lists the transactions of session `s` in session
   order, sessions nonempty); `SO` and `splice(H)` are derived from it. Every finite history whose `SO` is a union
   of total orders is of this form up to renaming of transactions.
9. **`max_R(A)`** is the predicate `IsMaxBy R A a`; the paper's convention "the use of `max` implicitly assumes it
   is defined" is built into EXT as an existential.
10. **Dependency graphs** (Definition 6): `RW` is derived from `WR`, `WW` by a definition (`DepGraph.RW`), not a
    field; the sets `GraphSER/SI/PSI` include the conditions of Definition 6 (the paper lets `G` range over
    dependency graphs). `graph(X) = G` is equality of the tuples `(𝒯, SO, WR, WW)`.
11. **Cycles** (§A.5) are nonempty closed walks (vertices may repeat) given as lists of (label, target) pairs.
    "Two adjacent anti-dependency edges" is `CycAdj`: two cyclically consecutive edges, including last–first; a
    one-edge cycle has no adjacent pair (irrelevant: `RW` is irreflexive). If the paper's "cycle" means a simple
    cycle, Theorems 19 and 22 are unaffected: a closed walk with no two adjacent `RW` edges (resp. with at most one
    `RW` edge) splits at a repeated vertex into two shorter closed walks, one of which keeps the property (the
    argument of `lemma24`), so both readings give the same conditions.
12. **Critical cycles** (§5): (i) no repeated vertex; (ii) some rotation of the label sequence starts with
    "conflict, predecessor, conflict"; (iii) for every rotation starting with an `RW` edge and every later `RW`
    edge, a `WR` or `WW` edge lies strictly between them (this covers both arcs between any two `RW` edges).
    `IsCriticalIn` is defined for any labelled graph and used for both `DCG(G)` and `SCG(P)`. Reading (ii)
    cyclically is the natural reading for a cycle; reading (iii) on both arcs makes fewer cycles critical, so the
    hypothesis "no critical cycle" of Theorem 16 and Corollary 18 is weaker than under a one-arc reading, and the
    Lean theorems are at least as strong as the paper's.
13. **Theorem 16** is proved in the stronger form of §A.5: for the paper's `splice(G)` (equation (2)),
    `splice(G) ∈ GraphSI` (`theorem16_splice`); spliceability (`theorem16`) follows.
14. **Corollary 18.** Programs are abstracted by `kᵢ` and the read/write sets `Rⱼⁱ`, `Wⱼⁱ`. "`H` can be produced by
    `P`" is: an injective assignment of programs to sessions, the `j`-th transaction of a session corresponds to
    the `j`-th piece of its program (`j < kᵢ`; a session may have fewer transactions than pieces), and every
    object read (resp. written) by an operation of the transaction lies in the piece's read (resp. write) set.
15. **Theorems 8 and 21** are cited by the paper (Adya; DISC 2015). We prove them (with preservation of the
    dependency graph, `theorem8_soundness`, `theorem21_soundness`), so Theorems 19 and 22 have their intended
    meaning in terms of histories.

## Not formalized

- The equivalence of the axiomatic definition of SI (Definition 4) with the operational SI concurrency control
  (cited from [10]).
- §B: Theorems 29 and 31 (chopping under serializability and parallel SI, cited) and the comparisons of the three
  chopping criteria; the static robustness analyses of §6 beyond Theorems 19 and 22.
- Most worked examples (Figures 4–6, 11–13); `Examples.lean` covers the anomalies of Figure 2 listed in the README.

## Typos (no effect)

- §6.1: "the dependency graph `G₄` of the long fork anomaly in Figure 4" should be Figure 2(c).
- Proof of Theorem 10(i): "in Figure 3 the transactions `T'` and `T''` are unrelated" should be Figure 4.
