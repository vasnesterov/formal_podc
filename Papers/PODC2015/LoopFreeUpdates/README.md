# Scheduling Loop-free Network Updates — PODC 2015

Arne Ludwig, Jan Marcinkowski, Stefan Schmid. *Scheduling Loop-free Network Updates: It's Good to Relax!*
PODC 2015. DOI [10.1145/2767386.2767412](https://doi.org/10.1145/2767386.2767412). Formalized version: the
10-page proceedings version (no arXiv version exists); numbering follows it.

**Verdict: ⚠️ Weakened.** The NP-hardness reduction for 3-round schedules is wrong: Theorem 2 is false, the paper's
network has no strongly loop-free 3-round schedule even for satisfiable formulas such as `x ∨ y ∨ z`, and so Theorem 1
(NP-completeness for `k = 3`) is unestablished; we neither prove nor refute it. The other results hold: the 2-round
characterization, the Ω(n) lower bound of Fig. 2 (exactly `n − 1` rounds), and the `O(log n)` bound for Peacock with
relaxed loop-freedom (Theorem 3, Lemmas 2–3). So the case for relaxing survives, resting on `Ω(n)` against `O(log n)`.

## Mistakes in the paper

### ❌ Theorem 2 (§3.2 reduction for 3-round schedules), hence the NP-hardness of Theorem 1
Theorem 2 is false: for a variable `x` set true by a satisfying assignment, round 2 of the claimed schedule
contains a forwarding ring through the exclusive gadget, and every other choice of round-1 copies closes one
of the paper's own gadget cycles, so the reduction maps satisfiable formulas such as `x ∨ y ∨ z` to
no-instances (`gadget_cycle`, `theorem_2_false`).

**Impact.** NP-hardness of the 3-round problem (Theorem 1) has no valid proof in the
paper; we neither prove nor refute it. The ring seems inherent to the gadget design, since an implication
gadget must lead from the consequent back to the antecedent.

**Details.** Theorem 2 claims that if the copies set to true by a satisfying assignment of `C′` are updated
in round 1 (and all `BB` nodes in round 2), the second round is cycle-free. Take any variable `x`, say with
one positive and no negative occurrence (every variable of `x ∨ y ∨ z`), and set `x` true. Then the second
round contains the ring
`x₀ ⇢ x₁^IN → x₁ ⇢ x_l^IN → x_l ⇢ v₃ → v₄ ⇢ x̄_l^H → x̄_l^IN → x̄_l → x̄_l^BB ⇢ x̄₀^H → x̄₀ → v₁ᴬ ⇢ v₂ᴬ → x₀^H → x₀`.
(⇢ = new rule, → = old rule.)
- The true copies jump forward along their implication edges.
- `x_l`'s dashed edge enters the exclusive gadget, and `v₄`'s `BB` edge leads to the false copy `x̄_l`.
- The implication `BB` edges then lead backwards through all false copies to `x̄₀`.
- Finally the assignment clause's path and its `BB` edge lead back to `x₀`.

Every edge is one the paper draws, with the colours it prescribes. The proof's claim that from `x_l` "there
is no way back" overlooks the exclusive gadget. Every other choice of round-1 copies violates a clause of
`C′` and closes one of the paper's own gadget cycles. So no choice of round-1 nodes makes the second round
cycle-free (formalized for a variable with `pₓ = 1`, `nₓ = 0`; the same argument works for any `pₓ, nₓ`, so
the network of every formula is a no-instance).

Lifted to instances: every network containing these gadgets with the required node types has no 3-round
schedule (`not_hasSLF_three_of_realizes`, non-vacuous by `realizes_example`). This covers every completion
of the under-specified connection step §3.2.4 that keeps the gadget edges and node types, as the paper says
its completion does (it only adds nodes above the vertical paths and in `R`).

### ✏️ Slips
- Lemma 1 says "the same holds true for nodes of type FF"; read literally, all `FF` nodes of a 3-round schedule can be
  moved to round 1, which is false for the 7-node instance with new route `0, 5, 4, 1, 3, 2, 6`
  (`lemma_1_FF_literal_false`). There a 3-round schedule exists, but with both `FF` nodes `0, 1` in round 1 the `BB`
  node `4` closes the loop `1 ⇢ 3 → 4 ⇢ 1` in round 2. The literal reading would also make the 3-round problem
  trivial, and the paper's own Fig. 4 shows why it fails. The proof moves nodes only from round 2 to round 1, and that
  intended version holds, also in the backward direction (`lemma_1`, `lemma_1_backward`).
- Lemma 2 ("reduces the number of nodes on the path by `n_t/3`") is true only when the updated start nodes
  are merged into their new successors, as §4 does, but not if they are counted as path nodes (old route
  `0,1,2,3`, new route `0,2,1,3`).
- Algorithm 1, line 7, ranges over all of `X` instead of the forward edges sorted in line 6.

### Typos
- §3.2.3 places `x_l^H` "just below `x_l` on the first path" while also saying `v₂` points "back to the second solid
  path"; Fig. 6 and the paper's listing of its cycle settle it.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Centralized scheduling of a single route update; no failures, no randomness. An instance is the paper's
  reduced line representation (§2): two duplicate-free lists `old` (r₁) and `new` (r₂) over the same nodes,
  both from `s` to `d` (`Instance`, `Model.lean`). A state is the set of updated nodes; each node forwards
  along its new rule if updated and its old rule otherwise (`fwd`).
* Asynchrony within a round is modelled as in the paper: in round `t` every state `U_{<t} ∪ X`, `X ⊆ U_t`,
  must be loop-free. Strong loop-freedom (`LoopFree`) = no directed cycle; relaxed (`RelaxedLoopFree`) = no
  cycle reachable from `s`, equivalently the walk from `s` reaches `d` (`relaxedLoopFree_iff`).
* Schedules are lists of pairwise disjoint rounds covering the nodes with `out₁ ≠ out₂` (`IsSLF`, `IsRLF`).
  Node types `FF, FB, BF, BB` as in §3.1.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| §3.1: 2-round schedule ⇔ no `BB` node | `Instance.hasSLF_two_iff` | `Rounds.lean` |
| round 1 only `F·`, last round only `·F` | `Instance.dashedFwd_of_mem_first`, `Instance.solidFwd_of_mem_last` | `Rounds.lean` |
| Lemma 1 (as proved: round 2 → round 1; backward: round 2 → round 3) | `Instance.lemma_1`, `Instance.lemma_1_backward` | `Rounds.lean` |
| Lemma 1, `FF` part read literally: **false** | `lemma_1_FF_literal_false` | `Lemma1.lean` |
| §3.2.1 normal form of 3-round schedules | `Instance.hasSLF_three_iff` | `Rounds.lean` |
| Theorem 2 (⇒): **false** | `gadget_cycle`, `theorem_2_false` | `Gadget.lean` |
| §3.2.4 reduction: instances with the gadgets have no 3-round schedule | `not_hasSLF_three_of_realizes`, `realizes_example`, `gadgetInstance_not_hasSLF_three` | `Gadget.lean` |
| Fig. 2: SLF needs exactly `n − 1` rounds | `fig2_slf_lower`, `fig2_not_hasSLF`, `fig2_hasSLF` | `LowerBound.lean` |
| §2.2: Fig. 2 has a 3-round RLF schedule | `fig2_hasRLF` | `LowerBound.lean` |
| "This is worst possible": `n − 1` SLF rounds always suffice | `Instance.hasSLF_card_sub_one` | `LowerBound.lean` |
| Algorithm 1 (Peacock) | `Instance.peacock`, `Instance.greedy`, `Instance.greedy_good` | `Peacock.lean`, `PeacockSelect.lean` |
| odd (shortcut) rounds are loop-free | `Instance.GoodSelection.odd_round` | `PeacockReduce.lean` |
| Lemma 2 (path shrinks by ≥ `n_t/3`, after merging) | `Instance.GoodSelection.lemma2`, `Instance.GoodSelection.reduce_length` | `PeacockCount.lean` |
| Lemma 3 (prune round is RLF; merging gives a line) | `Instance.GoodSelection.even_round`, `Instance.reduce`, `Instance.GoodSelection.rlf_of_reduce` | `PeacockReduce.lean` |
| Theorem 3: RLF schedule with `≤ 2 log_{3/2} n` rounds | `Instance.theorem3`, `Instance.exists_rlf_log` | `Peacock.lean` |

**Not formalized.** Theorem 1 (NP membership, and NP-hardness, which remains open here); the running time
of Peacock; Appendix A (greedy schedules).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Concrete counterexamples are checked by `decide` (walks are run with fuel, `loopFree_of_iterFrom`).
Non-vacuity: `realizes_example` exhibits an instance containing the gadgets; `lemma1Instance_hasSLF` and
`fig2_hasSLF`/`fig2_hasRLF` exhibit schedules. The model is self-contained (Mathlib only).
