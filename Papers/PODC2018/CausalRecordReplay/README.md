# Optimal Record and Replay under Causal Consistency — PODC 2018

Russell L. Jones, Muhammad S. Khan, Nitin H. Vaidya. *Brief Announcement: Optimal Record and Replay under
Causal Consistency.* PODC 2018. DOI [10.1145/3212734.3212789](https://doi.org/10.1145/3212734.3212789).
Formalized version: arXiv [1805.08804](https://arxiv.org/abs/1805.08804) v2 (full version with all
proofs); numbering follows it.

**Verdict: 🛠️ Hard fix.** All optimality results hold under strong causal consistency: the
offline records for both RnR models are good and least (Theorems 5.3, 5.4, 6.6, 6.7), and the online record
for Model 1 is good and least among online schemes (Theorems 5.5, 5.6). Definition 6.4 and the notion of
online record need small fixes, both available from the paper's own proofs, and the proofs of two central
results, necessity in Theorem 6.7 and sufficiency through Lemma C.1(b), needed new arguments.

## Mistakes in the paper

### 🔧 Theorem 5.6 (notion of "online record")
"`R` is an online record of `V`" is defined for one fixed execution, and in that reading any record of `V` is
online, so Theorem 5.6 would contradict Theorem 5.3.

**Impact.** The intended reading quantifies over recording schemes whose decisions depend only on the
recording process's knowledge, uniformly over all executions. In that reading Theorem 5.6 holds
(`theorem_5_6`).

**Details.** The paper also lets process `i` "check if `(o₁, o₂) ∈ SCO(V)`". We restrict `i`'s knowledge to
the prefix of its own view and, for each observed write of `j`, the prefix of `V_j` up to it (`SameKnow`).
That is exactly the paper's bound "process `i` is aware of `(o₁, o₂) ∈ V_j` only if it has observed some
`o³ⱼ` with `o₁ <_{V_j} o₂ ≤_{V_j} o³ⱼ`", it determines every SCO pair between operations `i` has observed,
and it is all the proof of Theorem 5.5 uses. A scheme online for less knowledge is online in our sense, so
this is the strongest form of Theorem 5.6. An oracle answering SCO queries about writes `i` has not
observed yet would exceed this bound and would break Theorem 5.6. This remark is argued on paper only, not
in Lean. Example: processes 1, 2, 3 write `w₁, w₂, w₃`; `V₁ = w₁w₂w₃`, `V₂ = w₂w₁w₃`, `V₃ = w₁w₃w₂`.
Then `(w₁, w₂)` is a `B₁` edge outside `SCO₁ ∪ PO`. When 1 observes `w₂`, the answers
`(w₁,w₃) ∈ SCO` and `(w₂,w₃) ∉ SCO` reveal `w₁ <_{V₃} w₂`. The scheme "record `V̂_i \ (SCO_i ∪ PO)` except
the `B_i` edges the oracle reveals" contains the offline record of Theorem 5.3, so it is good, yet it omits
`(w₁, w₂)`.

### ✏️ Slips
- Definition 6.4 (and hence Theorem 6.6) omits `w₃ ≠ w₄`. Read literally, `C¹_i(V, o₁, w₂)` contains the
  self-loop `(o₁, o₁)` whenever `o₁` is a write of `i`, so `B_i(V)` swallows such edges and Theorem 6.6's
  record is not good: two processes each write `x` once, both views order `w₁` before `w₀`, the record is
  empty, yet swapping both views is a valid replay with other data races (`theorem_6_6_literal_false`).
  The intent is evident: the proof of Lemma C.1(a) uses "`w³ ≠ w⁴₁`, by Definition 6.4", and the
  definition's wording "two write operations" suggests distinct ones. With `w₃ ≠ w₄` added at every level,
  Theorems 6.6 and 6.7 hold (`theorem_6_6`, `theorem_6_7`).
- Lemma C.1(a), Case 1 of the proof: the record is written `Â₁(V) \ (SWO(V) ∪ PO ∪ B₁(V))`. The lemma's
  statement, and Theorem 6.6, have `SWO₁(V)`. With `SWO` the four cases miss the edges in
  `SWO(V) \ SWO₁(V)`, and for that record the lemma would indeed fail (`lemma_C_1_SWO_record_false`).
  With `SWO₁`, as stated, the case split is complete.

### Typos
- Theorem 6.7, proof, read case: `(o³, w⁴)` should be `(w³, w⁴)`.

## Proof gaps (statements true)

### 🛠️ Theorem 6.7 (construction of the replay)
The proof's `U₁ = A₁(V) \ {(o₁,o₂)} ∪ {(o₂,o₁)} ∪ C₁(V,o₁,o₂)` is not a partial order whenever `o₁` is a
write of another process and `o₂` a write of process 1, because then `(o₁,o₂) ∈ C¹₁` (take `w₃ = o₁`,
`w₄ = o₂`).

**Impact.** Statement true; repaired with a different set of forced constraints (`theorem_6_7`).

**Repair.** The forced constraints `F` are computed in the *new* order of process `i`: `F⁰` uses
`A_i \ {(o₁,o₂)}` instead of `A_i`, and so do the propagation steps at process `i`. Then `F ⊆ C`, so
`¬B_i` gives acyclicity. Every `F`-target `z` satisfies `(o₂, z) ∈ F`, so `(o₂,o₁)` closes no cycle. The
strong causal pairs of `U` lie in `SWO(V) \ {(o₁,o₂)} ∪ F`. The paper's own case "`o₂` a read" fits as `F ⊆ SWO`.

### 🛠️ Lemma C.1(b) (bad write pairs, Claims C.2 and C.3)
The reduction from a violated `B_i` edge `(o, w′)` to the "bad write pair" `(wᵢ^min, w′)` silently changes
the `m = i` clause of Definition 6.5 (which removes a different pair), and the cycle surgery in Claim C.3
builds cycles that may use the removed pair `(wᵢ¹, w²)`.

**Impact.** Statement true; repaired with a new proof (`cov_preserved`, `lemma_C_1_b`).

**Repair.** Pick a violated cover of some `A_i(V)` whose `wᵢ^min` `u` is `SWO(V)`-maximal, preferring one
that starts at `u`. Claim C.2 then holds as in the paper (`stepA`). For Claim C.3 (`stepB`), one shows by
induction on the level of `C` (`lemmaX`) that no cycle of `(A_i \ {(u,w)}) ∪ C` enters `u` through a `C` edge.
Hence every `A_m(V)` segment of the cycle starts at a `C`-target other than such a `u` and is preserved
in `V'`.

### 🔧 Theorem 5.6 (indistinguishable execution)
The proof argues that "both orders are valid for future observation" but never builds a strongly causal
execution indistinguishable to process `i` in which the edge is not a `B_i` edge, which is what is needed
to invoke Theorem 5.4.

**Impact.** Statement true (in the uniform reading above); repaired (`exists_indistinguishable`).

**Repair.** Keep every known prefix. Order all unknown operations by one global strict total order that
puts known writes first, extends `SCO(V)` and `PO`, and orders `w₂` before `w₁`. This order exists by
`extend_partialOrder`.

### 🔧 Lemma A.1(b), Case 4
The proof uses the maximality of `wᵢ¹` with respect to `SCO(V)`, but derives only `(wᵢ¹, o^{ρ,j}) ∈ SCO(V′)`.

**Impact.** Statement true; `(wᵢ¹, o^{ρ,j}) ∈ SCO(V)` holds as well, because `o^{ρ,j}` is a write of
process 1 after `wᵢ¹` in `V₁` (`lemma_A_1_b`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Shared memory with read/write operations on variables (Section 2). There is a finite set of operations,
  each with a process, a kind and a variable. Program order is a strict total order on each process's
  operations and is fixed across executions. Processes are an arbitrary type.
- An execution is a writes-to map. A view of process `i` is a strict total order on `Obs i` (own operations
  and all writes) in which every read returns the last write before it (`IsViewOf`, `Explains`).
- Strong causal consistency (Definitions 3.3, 3.4): `SCO(V)` and `V_i ⊇ (SCO(V) ∪ PO|Obs i)⁺`.
- Records and replays are those of RnR Models 1 and 2 (Section 4). A replay is any execution explained by
  strongly causal views respecting the record. Its read values are unconstrained, and every family of total
  orders explains some execution (`exists_explains`).
- The transitive reduction `Â` is the cover relation `Cov`. For finite strict partial orders it is the
  unique minimal relation generating the order (`transGen_cov_eq`, `cov_le_of_transGen_eq`).
- Online setting (Section 5.2): a record scheme is online if its decision for `(o₁, o₂)` at `i` depends only
  on `i`'s knowledge when it observes `o₂` (`SameKnow`, `IsOnline`).
- No failures, no randomness; the adversary chooses the original and the replay views.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma A.1 (a), (b) | `lemma_A_1_a`, `lemma_A_1_b` | `Offline1.lean` |
| Theorem 5.3 | `theorem_5_3` | `Offline1.lean` |
| Theorem 5.4 | `theorem_5_4`, `rec1_least` | `Offline1.lean` |
| Theorem 5.5 | `theorem_5_5` | `Online1.lean` |
| Theorem 5.6 | `theorem_5_6`, `rec1on_least_online` | `Online1.lean` |
| Observation 6.3 | `obs_6_3` | `Model2.lean` |
| Observations B.2, B.3 | `not_B2_of_C0_sub`, `wmin_le_Ck_target` | `Sufficiency2.lean`, `Model2.lean` |
| Lemma C.1 (a), (b) | `lemma_C_1_a`, `lemma_C_1_b` | `Sufficiency2.lean` |
| Theorem 6.6 | `theorem_6_6` | `Sufficiency2.lean` |
| Lemma C.5 | `lemma_C_5` | `Completion.lean` |
| Theorem 6.7 | `theorem_6_7` | `Necessity2.lean` |
| Definition 6.4 / Theorem 6.6 literal (false) | `theorem_6_6_literal_false` | `Counterexamples.lean` |
| Lemma C.1 with Case 1's typo `SWO(V)` (false) | `lemma_C_1_SWO_record_false` | `Counterexamples.lean` |

**Not formalized.** The examples of Figures 2–10 (Sections 5.1, 6.1) and the negative examples for causal
consistency (Sections 5.3, 6.2) are not in Lean. We only tested them with brute-force Python scripts, which
are not part of this folder, and found that all claims there hold. This is evidence, not a verification.
Before the Lean proofs were finished, the same scripts also tested Theorems 5.3/5.4 and 6.6/6.7 on all
programs with up to 3 processes and 4 operations. The Lean proofs do not depend on those tests.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The counterexamples are concrete strongly causal executions, so the hypotheses of Theorems 6.6 and 6.7 are
satisfiable. The model is self-contained (Mathlib only). The generic order lemmas in `Basic.lean`
(covers, chain induction) and `Completion.lean` (one-process linear extension preserving SCO pairs) are
CSLib candidates.
