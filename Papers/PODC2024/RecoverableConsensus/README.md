# Recoverable consensus numbers — PODC 2024

Sean Ovens. *Determining Recoverable Consensus Numbers.* PODC 2024. DOI
[10.1145/3662158.3662775](https://doi.org/10.1145/3662158.3662775). Formalized version: arXiv
[2405.04775](https://arxiv.org/abs/2405.04775) v1.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main result (Theorem 13: a set of deterministic types solving recoverable
wait-free consensus among `n` processes contains an `n`-recording type) is proved, following the paper's proof.
Section 4's separation (`T_{n,n'}` has consensus number `n` and recoverable consensus number `n'`) is also true,
but one step of the proof of Lemma 15 is false and the proof of Lemma 16 has a non-symmetric "symmetric" case;
both are repaired.

## Mistakes in the paper

1. **Lemma 15, case `o_i = opR` (false claim in the proof; statement true).** The proof claims that if `p_i` (team
   `v`) applies `opR` then `value(O, C′p_ip_j) = value(O, C′p_j)` for any `p_j` on team `v̄`, "in either case".
   This fails when `value(O, C′) = s_{x,t}` with `n′ < t < n − 1` and `p_j` applies `op_y`: after `p_i p_j` the
   object is `s⊥`, but after `p_j` alone it is `s_{x,t+1}`. Repair: in this case `p_i` reads `⊥` both in `C′p_i`
   and in `C′p_jp_i`, and `O = s⊥` in both, so the two configurations are already indistinguishable to `p_i`
   (no third process is needed). The same comparison is reused in Lemma 16 (`lemma15`, `lemma16`).
2. **Lemma 16, proof (gaps; statement true).** "The case `j < i` is symmetric" is not: the crash of `p_j` is
   within `E*_z`'s crash budget only when a process with a smaller identifier has already stepped. The crash-free
   comparison of item 1 handles both orders. Also in the `ρ, τ` construction: the bound `ℓ < n − n′ − 1` is off by
   one (harmless for the budget), and the claim that `p_{n′}` has decided in `Cασ₀ρ_ℓ` fails when `O` becomes
   `s⊥`; the contradiction follows directly from equal memory and equal state of the last process.
3. **Section 3 imprecisions (no step fails).**
   - *Observation 5* is stated for any `C′ ∼_{P′} Cα` with equal object values, but fails if a process outside
     `P′` has already decided the other value in `C′` (and with the paper's history-based "decided" it is not
     well defined for arbitrary `C′`). An extra hypothesis (nobody outside `P′` has output) holds in every use,
     since those processes are in their state at a critical configuration.
   - *Agreement* must cover two outputs of the *same* process in different incarnations; Lemma 6's proof needs
     this, the paper's wording ("no two processes") does not say it.
   - Lemma 6 (and 7–10, 12) implicitly assume `C` is reachable — the usual valency convention.
   - Observation 2's converse is not justified by the paper (only the forward direction is used); Lemma 7 does not
     treat the case where `β_{v̄}` is empty; Lemma 12 needs that all processes are poised on a common object,
     which follows from Lemma 9 but is not stated.
4. **Remark on readability.** `T_{n,n'}` is called non-readable for all `n > n′ ≥ 1`. For `n′ = n − 1`, `opR`
   never changes the value and its response determines it, so it is a read up to encoding `s⊥` as `⊥`
   (`readable_Tnn_pred`). No theorem is affected.
5. **Typos.** Observation 2 "`P` is univalent" (should be `P′`); Lemma 12 "`E*_z(C′Xλ_k)`" (should be
   `E*_z(CαXλ_k)`); Lemma 16 `τ_{i+1} = ρ_iδ′…` (should be `τ_iδ′…`), first invariant `Cασ₀ρ_i ∼ Cασ₀τ_i`
   (should be `Cασ₁τ_i`), and a missing "is" in its statement.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib, `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`; object families `withRW` and
the progress tool `prog_of_rank` from the shared library `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`).
- Asynchronous shared memory, `n` deterministic processes `Fin n`, arbitrarily many objects with deterministic
  sequential specifications, initial values chosen by the algorithm. Each step of a non-output process is one
  operation on one object; steps in output states are no-ops. No randomization.
- Individual crash-recovery: the adversary schedules steps and crashes; a crash resets the process to its initial
  (input-determined) state, shared objects are non-volatile. Simultaneous crashes are not modelled (the paper
  does not use them).
- Binary consensus. Recoverable wait-freedom (`RecConsensus`): in every infinite execution, a process that takes
  infinitely many steps and stops crashing after time `N` is in an output state at some time `≥ N`. Wait-freedom
  (`WFConsensus`) is the same on crash-free executions. Registers are generalized to any read/write-like objects (`ObjSpec.RWLike`).
- Ovens' bounded-crash execution sets `E_z`, `E*_z` and valency are defined on event lists from a base
  configuration, as in the paper. Consensus numbers quantify over all `m > n` processes.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemmas 6–9 (critical configurations, teams, poised) | `exists_crit`, `Crit.teams`, `Crit.biv`, `Crit.poised` | CSLib `Recoverable.lean` |
| Lemma 10, Observation 11, Lemma 12 | `lemma10`, `obs11`, `lemma12` | `Lemma12.lean`, `Config.lean` |
| **Theorem 13** | `theorem13` | `Theorem13.lean` |
| Theorem 14 (robustness), given DFFR'22 Thm 8 | `theorem14` (hypothesis `dffr`) | `Theorem13.lean` |
| Theorem 14 unconditionally (DFFR'22 Thm 8 proved in [RecoverableHarder](../../PODC2022/RecoverableHarder)) | `Podc.RecoverableHarder.ovens_theorem14` | `Papers/PODC2022/RecoverableHarder/Corollaries.lean` |
| Lemma 15: consensus number of `T_{n,n'}` is `n` | `lemma15` | `Sec4Lemma15.lean` |
| Lemma 16: recoverable consensus number of `T_{n,n'}` is `n'` | `lemma16` | `Sec4Lemma16.lean` |
| Golab: test-and-set cannot solve recoverable 2-consensus | `tas_not_recSolvable` | `Corollaries.lean` |

**Not formalized here.** DFFR'22 Theorem 8 (sufficiency of `n`-recording for readable types; a hypothesis of
`theorem14`) and Ruppert's characterization of consensus numbers are formalized in
[`Papers/PODC2022/RecoverableHarder`](../../PODC2022/RecoverableHarder) (`theorem8`, `theorem3`), which also
proves `theorem14` without the hypothesis (`ovens_theorem14`). The consequence for DFFR's type `X_n` is not formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `lemma16` contains a concrete recoverable wait-free consensus algorithm (`Sec4.alg16_recConsensus`),
so the hypothesis of Theorem 13 is satisfiable. Readability (`ObjSpec.Readable`, used only in Theorem 14) is formalized up
to encoding of responses.
