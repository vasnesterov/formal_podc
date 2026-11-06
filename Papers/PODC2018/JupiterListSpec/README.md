# Replicated List: the Jupiter Protocol Revisited — PODC 2018

Hengfeng Wei, Yu Huang, Jian Lu. *Brief Announcement: Specification and Implementation of
Replicated List: The Jupiter Protocol Revisited.* PODC 2018. Formalized version: full version,
arXiv [1708.04754](https://arxiv.org/abs/1708.04754) v4; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** The main results hold: once clients send in-range positions, Jupiter and CJupiter
behave identically (Theorem 12), are convergent (Theorem 11) and satisfy the weak list specification
(Theorem 18), which settles the conjecture of Attiya et al. As written, they fail: the paper lets users insert or
delete "at a position larger than the list size" (meaning at the end) and sends that position unchanged, so the
OT functions of Figure A.1 violate CP1 and both protocols diverge; the fix is one line, normalising the position
before sending. Several proofs of Section 5, on which Theorem 18 rests, are not real arguments, and we replace
them by a different argument.

## Mistakes in the paper

### 🔧 Figure A.1 with out-of-range positions (Theorems 11 and 18)
With positions beyond the list size, which Section 2.3 allows and the clients send unchanged, the OT
functions of Figure A.1 violate CP1 (`cp1_fails`), and both Jupiter and CJupiter diverge, violating
Theorems 11 and 18 (`jupiter_raw_counterexample`, `cjupiter_raw_counterexample`).

**Impact.** A local fix (one line of pseudocode) that the paper's own text supplies: normalise the
position when the operation is generated (`genOp`); with in-range positions Figure A.1 satisfies
CP1 (`square`) and all main results hold. The out-of-range convention is stated explicitly in the paper, so the
printed protocols really diverge.

**Details.** Section 2.3 defines `Ins(a, p)`/`Del(p)` for `p` beyond the list size as an
insertion/deletion at the end. The clients send `o` unchanged (Algorithms B.5, C.5), and the OTs of
Figure A.1 compare raw positions. On `[x]`: `o₁ = Del(5)` deletes `x`, and `o₂ = Ins(b, 1)`
appends `b`. Then `OT(o₁, o₂) = Del(6)` and `OT(o₂, o₁) = Ins(b, 1)`. Applying `o₂; Del(6)` gives
`[x]`, while `o₁; Ins(b, 1)` gives `[b]`. As a run of Jupiter with two clients: `c₀` inserts `x`;
then `c₀` deletes at 5 while `c₁` inserts at 1. Both final `Read`s see all three updates, yet `c₀`
reads `[b]` and `c₁` reads `[x]`. This violates `A_cp` and hence `A_weak`. The violation of
`A_weak` does not depend on the choice of the abstract execution: `c₁`'s final `Read` must see
`c₁`'s own `Ins(b, 1)`, nobody deletes `b`, yet it returns `[x]`. So no well-formed abstract
execution complying with the run is in `A_weak` (`cjupiter_raw_not_weak_any`,
`jupiter_raw_not_weak_any`).

The paper requires that a transformed operation "inserts (resp. deletes) the element `a`", which
only makes sense for in-range positions, and the OT literature it cites [8, 9] assumes them.

**Repair.** We normalise the position in `genOp`. The user-visible result does not change; only the
operation sent to the server does.

### ✏️ Slips
- Footnote 8's LCA definition (an antichain of common ancestors) does not say "lowest".

### Typos
- Appendix A says that the *smaller* replica id has the *higher* priority, while Figure A.1 shifts
  the insertion with the *larger* `pr`. With ids used as priorities (Figure A.1's caption),
  Figure 1 ends in `ab`, not `ba`. Either convention works.

## Proof gaps (statements true)

### 🛠️ Lemmas 23 and 24 (Theorem 26, pairwise compatibility)
Lemma 24, Case 2.2 ("step ladder") and the inductive step of Lemma 23 are not real arguments.

**Impact.** Statements true; we give a different proof (`Sched.Vert.inter`, `Sched.compatible`).

**Repair.** The vertices of the global state space are the causally closed operation sets made of
a `≺s`-prefix plus operations of one client. These sets are closed under intersection, so the LCA
of Lemma 23 is `V₁ ∩ V₂`. Along any path, the operations keep the relative order of existing
elements. Two common elements of `V₁` and `V₂` were therefore inserted in `V₁ ∩ V₂` and keep their
order on both paths.

### 🔧 Lemma 25 (one-step claim)
The one-step claim assumes the operation "does not correspond to any element of the list in `v`", which excludes deleting a common element, a case the induction needs.

**Impact.** Statement true: a deletion only shrinks the common elements and keeps their order
(`Sched.sublist_of_subset`, `Sched.compatible`).

### 🔧 Remark after Definition 19 (used in Lemma 21)
The remark that `lo` is transitive on each list "by definition" is only true *given* pairwise compatibility.

**Impact.** Statement true; transitivity follows from Theorem 26 (`Cfg.GI.weak`, `Sched.compatible`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n` clients and one server. Each client is connected to the server by two reliable FIFO
  channels; the system is asynchronous. An execution is any finite sequence of events: `do c u`
  (a user operation at `c`), `srv c` (the server processes the next message from `c`) and
  `recv c` (`c` processes the next message from the server). There are no failures and no
  randomness. The server generates no operations (as in the paper).
* Operation ids are `(client, seq)`. Inserted elements are these ids (the paper's "unique
  elements"). The priority of an insertion is its client id.
* Both protocols follow the pseudocode of Appendices B and C literally. A state space is the list
  of its edges (each labelled by an operation whose context is the source vertex) plus the current
  vertex. In Jupiter, the edge of `u` in dimension `d` is the latest-added matching edge, which
  mirrors the array overwrite of Algorithm C.4. CJupiter's `firstEdge` is the edge that `Compare`
  ranks below all others.
* `Read` also generates a `NOP` operation that is sent around, as `Do` does in the pseudocode. A
  `Del` on an empty list is recorded as `Del(⊥, k)`.
* An abstract execution has `H` = the `do` events in execution order. Its visibility is "the
  operation was processed by the replica before this event". This is a well-formed visibility
  relation (proved), but we do not prove that it coincides with Lamport's happened-before.
* Proof device: a *global state space* determined by a schedule (`Sched.T`, `Sched.L`). Its
  ranks are the server order, *prophesied* from the final configuration of the execution
  (pending operations come after the processed ones, in FIFO order).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| CP1 for Fig. A.1 (Sect. 2.4), in-range positions | `square` | `OT.lean` |
| CP1 fails for Fig. A.1 with the paper's out-of-range positions | `cp1_fails` | `OT.lean` |
| Thm 11/18 fail for the paper's literal model (Jupiter, CJupiter) | `jupiter_raw_counterexample`, `cjupiter_raw_counterexample` | `Counterexample.lean` |
| … for every compliant abstract execution (any `vis`) | `cjupiter_raw_not_weak_any`, `jupiter_raw_not_weak_any` | `Counterexample.lean` |
| Def. 1 (`A_weak`), `A_cp`, `A_weak ⊆ A_cp` | `AbsExec.Weak`, `AbsExec.Conv`, `AbsExec.Weak.conv` | `Spec.lean` |
| Lemmas 22–25, Thm 26 (pairwise compatibility) | `Sched.Vert.inter`, `Sched.sublist_of_subset`, `Sched.compatible` | `Space.lean` |
| Lemma 21 / Def. 19 / proof of Thm 18 | `Cfg.GI.weak` | `Weak.lean` |
| Lemmas 5, 7 (first rule, OT sequence) | `CJup.walk` | `CJupiterWalk.lean` |
| Prop. 9 (single state space) | `cjupiter_inv` (`CJup.CPI`) | `CJupiterMain.lean` |
| Thm 11 (CJupiter ⊨ `A_cp`) | `cjupiter_conv` | `CJupiterMain.lean` |
| Thm 18 (CJupiter ⊨ `A_weak`) | `cjupiter_weak` | `CJupiterMain.lean` |
| Props. 14, 16 (Jupiter's state spaces ⊆ CJupiter's) | `jupiter_inv` (`Jup.JPI`) | `JupiterMain.lean` |
| Thms 12, 15, 17 (equivalence) | `equivalence` | `CJupiterMain.lean` |
| Conjecture of Attiya et al.: Jupiter ⊨ `A_weak` | `jupiter_weak` | `JupiterMain.lean` |
| Jupiter ⊨ `A_cp`; replicas agree at quiescence | `jupiter_conv`, `jupiter_quiescent` | `JupiterMain.lean` |

**Not formalized.** The figures' step-by-step examples (we only ran Figure 1 as a test) and the
literal set equalities of Propositions 14 and 16. These are replaced by the invariants above,
which are stronger for what Theorems 12 and 18 need. Proposition 9, Lemma 5 and Propositions 14 and 16
are argued by "mathematical induction" sketches, and Prop. 9's hard Case 2 (an operation inserted in the
middle of a client's sequence) is only illustrated; we found no wrong step but did not check them, and
prove these facts as invariants instead. For CJupiter: every replica's state space is sound and complete
(`CPI`). For Jupiter: every 2D-state-space edge is an edge of the global space (`JPI`). Lemma 22
("parallel transitions") is a short sketch that we bypassed, and Lemma 21 was not checked as stated. That
the visibility used here coincides with Lamport's happened-before, the `vis` picked in the proof of
Theorem 18, is open.

**Trust.** No `sorry`. The listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity: the handlers never get stuck (`jupiter_srv_enabled`, `jupiter_recv_enabled`,
`cjupiter_srv_enabled`, `cjupiter_recv_enabled`), so every interleaving of user operations and
deliveries is an execution. The model is built from Mathlib only; it uses no CSLib modules.
