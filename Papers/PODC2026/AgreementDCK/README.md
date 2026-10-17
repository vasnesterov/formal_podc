# What is Agreement About if not Common Knowledge? — PODC 2026

Or David, Yoram Moses. *Brief Announcement: What is Agreement About if not Common Knowledge?*
PODC 2026. DOI [10.1145/3796701.3815934](https://doi.org/10.1145/3796701.3815934). Formalized version:
the 4-page proceedings brief announcement (we found no full version on arXiv); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The paper gives no proofs. We supplied them, and all the
results hold in the generic runs-and-systems model: knowledge of preconditions (Thm 1.2), necessity
of dynamic common knowledge (Thm 1.5, Cor 1.6) and sufficiency (Thm 1.7). One clause of Theorem 1.7
("the nonfaulty processes decide `v` in `r` iff `r ⊨ θ_v`") is false in runs with no nonfaulty
process. The informal converse remark after Theorem 1.7 needs nonfaulty processes to remember their
decisions.

## Mistakes in the paper

* **Theorem 1.7, the "iff" clause: false only in a degenerate case.** `all_decide(v)` holds
  vacuously in a run with `N(r) = ∅`, but `θ_v` need not hold there. Exclusivity even forbids `θ_v`
  for two different values, while `all_decide(v)` holds for all of them. Counterexample: one run,
  every process faulty, all `θ_v` false. All hypotheses of Theorem 1.7 hold trivially. Fix: assume
  `N(r) ≠ ∅`, which most models do (`f < n`). The other claims of Theorem 1.7 hold unchanged.
  (`theorem_1_7_iff_false_without_nonfaulty`, repaired: `allDecide_newDec_iff`)
* **The converse remark needs memory of decisions (imprecise informal claim).** The paper says
  "underlying the design of every AoN protocol is a set of facts Θ as described in Theorem 1.7".
  We read Θ as facts that describe the protocol's decisions. With that reading the remark holds when
  nonfaulty processes remember their decisions: take `θ_v` = "some nonfaulty process decides `v`"
  and the profile `𝛅(v)` (`exists_theta_of_AoN`). Without such recall it fails. Example: one
  failure-free process learns a bit `b` at time 1, decides `b` then, and forgets `b` afterwards. This
  protocol is AoN and satisfies Agreement, Validity and Decision. Yet no local, remembered profile
  makes `θ_v ↔ all_decide(v)` even dynamically *everyone*-known, let alone dynamic common knowledge.
  (`no_theta_for_forgetful_protocol`)
* **Minor points (no error).**
  - Theorem 1.7's hypothesis `⊨ θ_v → C^N@𝛙(v)(θ_v)` is equivalent to the weaker-looking
    `⊨ θ_v → E^N@𝛙(v)(θ_v)`, by the induction rule (`sufficient_of_EN`).
  - The assumption that `P` solves `A` is never used.
  - The memory hypothesis is used only to make the new decisions stable ("conscious").
  - Corollary 1.6 needs `AoN(v)` only for the decided value `v`, and it holds for every
    precondition of deciding `v`, as the text says (`KN_CN_of_precondition`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The generic runs-and-systems model (`Cslib/Computability/Distributed/Knowledge/Basic.lean`). A system is an arbitrary type
  `R` of runs with time `ℕ`, and local states `loc i r t` for each process `i`. Each run has a set
  `nf r` of nonfaulty processes; the failure model is abstract, as in the paper. Facts are
  predicates on points; run facts are time-independent facts. `K_i` quantifies over all points of
  all runs with the same local state of `i`. No synchrony, communication or failure assumptions are
  needed, matching the paper's claim "in all models". The modalities are those of the shared
  indistinguishability system `System.toIndist` (`IndistSystem.K`, `KN`, `kop`, …), used also for
  the knowledge notions of KMO'11 and of CSLib's synchronous crash model.
* `K_i^N φ = i ∈ N ∧ K_i(i ∈ N → φ)`, plus Kuznets et al.'s hope `H_i`. Dynamic knowledge, dynamic
  everyone-knows and dynamic common knowledge follow Definitions 1.3–1.4 verbatim.
* A protocol is its system plus decision facts `decideᵢ(v)`. Decisions are assumed `i`-local: this
  is the paper's standing assumption that decisions depend on the local state.
* Theorem 1.7 has no proof in the paper. We build `P_A` on the same runs: it adds the local decision
  rule `ψᵢ(v) ∧ K_i(i ∈ N → θ_v)`. The new decisions are outputs only and do not change local
  states or messages.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 1.1, footnote 4 (`K^N`, hope) | `System.KN`, `KN.holds`, `kn_iff_hope`, `hope_of_faulty` | `Cslib/Computability/Distributed/Knowledge/Basic.lean` |
| Theorem 1.2 (KoP for nonfaulty processes) | `System.kop`, `Decisions.theorem_1_2` | `Cslib/Computability/Distributed/Knowledge/Basic.lean`, `Necessity.lean` |
| Def. 1.3, 1.4 (`K_i^N@ψ`, `E^N@𝛙`, `C^N@𝛙`) | `System.DK`, `System.EN`, `System.EIter`, `System.CN` | `Dynamic.lean` |
| Remarks after Def. 1.4 (correct processes eventually know DCK) | `CN.eventually_KN`; also `CN_iff_EN`, `CN_of_EN_valid` | `Dynamic.lean` |
| Theorem 1.5 | `Decisions.theorem_1_5` (general form `KN_CN_of_precondition`) | `Necessity.lean` |
| Corollary 1.6 | `corollary_1_6_validity`, `corollary_1_6_noDec` | `Necessity.lean` |
| Theorem 1.7 | `theorem_1_7`, `allDecide_newDec_iff`, `sufficient_of_EN` | `Sufficiency.lean` |
| Theorem 1.7 "iff" without nonfaulty processes: **false** | `theorem_1_7_iff_false_without_nonfaulty` | `Sufficiency.lean` |
| Converse remark (every AoN protocol has a Θ) | `exists_theta_of_AoN`; needs memory: `no_theta_for_forgetful_protocol` | `Sufficiency.lean` |
| Motivation: DCK without common knowledge | `Example.example_CN`, `Example.example_not_C` | `Example.lean` |

**Not formalized.** The applications that the paper leaves to its full version: the crash-failure
Consensus protocol, Bracha's reliable broadcast, and committees.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`; several use none.

Non-vacuity (`Example.lean`): two processes, no failures, and one asynchronously delivered message
carrying a bit. This protocol satisfies AoN, Agreement, Validity, Decision and stable decisions, so
the hypotheses of Theorems 1.5 and 1.7 are satisfiable (`example_sufficient`). In every run,
`all_decide(b)` is dynamic common knowledge. Yet classical common knowledge of the bit, even
`E²`, holds at no point. This is the paper's motivating claim that DCK is strictly weaker than CK.

Upstreamed to CSLib: `Cslib/Computability/Distributed/Knowledge/Basic.lean` (indistinguishability systems and interpreted
systems: `K`, `K^N`, hope, KoP, `E`/`C` with `C_iff_forall_reach`).
