# Fair and Resilient Incentive Tree Mechanisms — PODC 2013

Yuezhou Lv, Thomas Moscibroda. *Fair and Resilient Incentive Tree Mechanisms.* PODC 2013. DOI
[10.1145/2484239.2484252](https://doi.org/10.1145/2484239.2484252). Formalized version: the journal version
(Distributed Computing 29(1), 2016, DOI 10.1007/s00446-015-0250-y, author copy, full proofs in the appendix);
all theorem, lemma, section and algorithm numbers below are the journal's. The PODC 2013 version (10 pp,
proof sketches only) numbers the same results differently: Theorems 1–4 = PODC Theorems 4.1–4.4,
appendix Lemmas 1–5 = PODC Lemmas 4.5–4.9, Theorem 5 = PODC Theorem 4.10; journal Sections 4.4, 5, 6 =
PODC Sections 4.2, 4.3, 4.4. The two versions state the definitions of Section 3 identically (in particular
PO with `R(u) ≥ C(u)`).

**Verdict: ⚠️ Minor statement issues.** All four checked theorems hold once small slips are fixed. These are: the
impossibility result (Theorem 3), the geometric mechanism (Theorem 1), TDRM (Theorem 4: everything except UGSA,
in particular Sybil-proofness USA) and the CDRM family (Theorem 5: everything except URO, in particular UGSA).
The slips are a `≥` that should be `>` in the formal definition of PO (with it, Theorem 3 is false for budget
`Φ = 1`), Theorem 5 also losing PO, and zero contributions / zero parameters. The long appendix proof of TDRM's
USA (Lemmas 1–5) has gaps; we replace it by a short induction.

## Mistakes in the paper

### ⚠️ Section 3.1, definition of PO (makes Theorem 3 false as stated)
With PO formally defined as "`R(u) ≥ C(u)`" (zero profit suffices) and the allowed budget `Φ = 1`, the
mechanism `R(u) = C(u)` satisfies SL, PO, UGSA and the budget constraint, contradicting Theorem 3
(`theorem_3_false_for_weak_PO`).

**Impact.** Local fix: the prose of the same paragraph says PO means *positive* profit, and the proof of
Theorem 3 uses `P(v*) > 0`. With `R(u) > C(u)` Theorem 3 holds and the paper's proof is correct (`theorem_3`).

**Details.** `R(u) = C(u)` is subtree-local and has total reward `C(T) = Φ·C(T)`. Every node makes profit 0
whatever the shape of its subtree, so PO (weak) holds, and any Sybil split has total profit 0 = the single
node's profit, so UGSA (hence USA) holds. It also satisfies CCI and `φ`-RPC for every `φ ≤ 1`, but not CSI
or URO. Whether the weak-PO version of Theorem 3 holds for `Φ < 1` is open: the paper's argument needs a
strictly profitable node, and we neither proved nor refuted that case.

### ⚠️ Theorem 5 (CDRM mechanisms: "all properties, except URO")
A successfully contribution-deterministic mechanism also violates PO, since `R(x, y) < Φx ≤ x` (`theorem_5`).

**Impact.** Evident intent: Section 4.4 announces that the Section 6 mechanism "achieves all the properties except
PO/URO" and notes URO ⇒ PO. Everything else in Theorem 5 is proved, including UGSA.

### ⚠️ Zero contributions and zero parameters (Theorems 1, 4, 5)
Several claims fail only when a contribution or parameter is 0: CSI fails when the newcomer contributes 0 (all
mechanisms) or `C(u) = 0` (TDRM, CDRM), TDRM's chain for `C(u) = 0` has `N_u = ⌈0/μ⌉ = 0` nodes, Theorem 5 never
constrains `R(0, y)`, and Theorems 1 and 4 allow `b = 0` (if `φ = 0`) and `a, λ ≤ 0`, where CCI/CSI/URO fail.

**Impact.** Degenerate cases (R2/R4); we add the evident positivity assumptions (`0 < b` in Theorem 1;
`0 < a`, `0 < b`, `0 < λ`, `0 ≤ φ` in Theorem 4; right-continuity of `R(·, y)` at 0 in Theorem 5, which forces
`R(0, y) = 0`), use a one-node chain for `C(u) = 0`, and require positive contributions in CSI.

### ⚠️ Appendix, Lemmas 1–5 (structure of an optimal Sybil partition for TDRM)
The uniqueness parts ("must be an ε-chain", "at most one node below `μ`", "forms a tree") fail in degenerate
cases: Lemma 5 fails whenever `u` has no solicitees (then `R^e ≡ 0` and every partition maximizes it), and
Lemmas 1–3 fail when a Sybil identity contributes 0.

**Impact.** The proof of Theorem 4 only needs that *some* optimal partition is an ε-chain (which is what its
proof idea says), and Theorem 4's USA is proved without these lemmas (`tdrm_USA`).

### Typos and slips
- Algorithm 4 creates the RCT edge `(m^u_{N_u}, m^v_1)` for an edge `(u, v)`, but in Section 2 `(u, v)` means
  "`u` is a child of `v`"; Figure 3 shows the intended direction (tail of the parent → head of the child).
- The UGSA counterexample after Theorem 4: `P(u)` should be `½((ak + ½)λμb + φμ − μ)`, not `(ak + 1)`; the
  conclusion `P'(u) > P(u)` is unaffected (`theorem_4`, last conjunct).

## Proof gaps (statements true)

### 🛠️ Theorem 4 (TDRM satisfies USA; appendix Lemmas 1–5)
The proof argues about a reward-maximizing Sybil partition without showing that one exists, and its exchange
steps only weakly increase the reward (Lemma 2 case (b) even leaves a 0-contribution node below `μ`), so
"contradiction with maximality" does not follow.

**Impact.** Statement true; repaired with a new proof (`tdrm_USA`).

**Details.** The number of Sybil identities is unbounded and contributions are real, so the existence of an
optimum is itself what has to be shown; with weak improvements the contradiction scheme of Lemmas 1–5 would
have to be replaced by "some optimum has the structure", which presupposes the optimum. Also, Lemma 2's
auxiliary fact `S1 > S2` only covers transfers away from the balanced split; when `C(x) < C(y)` the transfer
towards `x` first passes through it, and what is needed is convexity of the quadratic in the transfer.

**Repair.** We compute the closed form `R(u) = (λb/μ)(Q(C(u)) + a·G(C(u))·X) + φC(u)` (`tdrm_node`). Here
`Q`, `G` are explicit functions of the ε-chain and `X` is the depth-weighted contribution of the children's
RCTs. We then prove by induction on the Sybil forest (`sybil_bound`) that a Sybil tree of mass `m` earns at most
`Q(m) + a·E·G(m)`, the single-node value. Every optimisation fact of Lemmas 1–5 reduces to five inequalities
about `Q`, `G`, `H` (`Qc_add`, `Qc_superadd`, `Hc_add_le`, `Gc_add_le`, `Gc_subadd`): concatenating chains never
loses, and branching loses at least what the extra ancestor weight gains.

### 🛠️ Theorem 5 (CDRM satisfies USA)
The minimal-counterexample merging argument is incomplete: merging can lower the reward of other Sybils, and
"at least the same reward" does not contradict minimality of `k`.

**Impact.** Statement true; repaired by a direct induction on the Sybil forest: a Sybil tree of mass `m` with
real contribution `E` earns at most `R(m, E)` (`theorem_5`; uses (iv) and monotonicity in `y`).

**Details.** In case (a) the merged ancestor–descendant pair need not be adjacent, which lowers the reward of
the Sybils in between; case (b) ignores Sybil ancestors of `p₂`, which lose `x₂ + y₂` from their subtrees.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Not a distributed-computing model: a mechanism maps a weighted referral tree (contributions `C(u) ≥ 0`) to
  rewards. No time, adversary or randomness. Sybil attacks are compared on final configurations, which
  under SL is the same as "for every `i`" along join sequences.
- Only subtree-local mechanisms are modelled: a mechanism is `f : Tree → ℝ`, the reward of the root of the given
  subtree. All mechanisms of Theorems 1, 4, 5 are of this form, and Theorem 3 assumes SL.
- Trees are rose trees with ordered children lists. Theorem 3 is thereby proved for a larger class
  (order-dependent mechanisms included); all our mechanisms are order-invariant.
- A Sybil attack of `u` is a forest of Sybil trees (`Sybil.node c sybilChildren realChildren`). Every real
  child subtree of `u` is attached to exactly one Sybil (up to permutation). With SL, where the Sybil trees
  are placed in the rest of the referral tree is irrelevant. Single-identity "attacks" (`k = 1`) are
  included, as in the paper's UGSA counterexample for TDRM.
- The budget is required over all nodes of every tree, including a root of contribution 0 (at least as strong as
  the paper's `R(T) ≤ ΦC(T)`). PO is "positive profit" (`PO`); the printed weak version is `POWeak`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3 (SL + PO + UGSA impossible) | `theorem_3` | `Impossibility.lean` |
| Theorem 3 with PO as printed (`≥`), false for `Φ = 1` | `theorem_3_false_for_weak_PO` | `Impossibility.lean` |
| Theorem 1 (geometric mechanism; fails USA/UGSA) | `theorem_1` | `Geometric.lean` |
| Algorithm 4 (TDRM) and its closed form | `tdrm`, `rct`, `tdrm_node` | `TDRM.lean` |
| Theorem 4 (TDRM: all but UGSA; UGSA counterexample) | `theorem_4` | `TDRMProps.lean` |
| Theorem 4, USA (appendix Lemmas 1–5) | `tdrm_USA`, `sybil_bound` | `TDRMProps.lean` |
| Chain inequalities behind Lemmas 1–5 | `Qc_add`, `Qc_superadd`, `Hc_add_le`, `Gc_add_le`, `Gc_subadd`, `chain_budget` | `TDRMChain.lean` |
| Theorem 5 (CDRM: all but URO and PO) | `theorem_5` | `CDRM.lean` |
| Algorithm 5 (i) satisfies the hypotheses of Theorem 5 | `cdrmExample_successfullyCD`, `theorem_5_example` | `CDRMExample.lean` |
| UGSA ⇒ USA, URO ⇒ PO (Section 3) | `UGSA.usa`, `URO.po` | `Basic.lean` |

**Not formalized.** Theorem 2 (L-Pachira, whose USA proof is imported from [7]), the split-proof mechanism of
Section 4.3, and Algorithm 5 (ii).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: Theorem 5's hypotheses hold for Algorithm 5 (i) (`theorem_5_example`). The hypotheses of
Theorems 1 and 4 are explicit parameter ranges. Self-contained (Mathlib only).
