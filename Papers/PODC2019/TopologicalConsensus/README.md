# Topological Characterization of Consensus under General Message Adversaries — PODC 2019

Thomas Nowak, Ulrich Schmid, Kyrill Winkler. *Topological Characterization of Consensus under General
Message Adversaries.* PODC 2019. DOI [10.1145/3293611.3331624](https://doi.org/10.1145/3293611.3331624).
Formalized version: the PODC'19 paper is arXiv [1905.09590](https://arxiv.org/abs/1905.09590) **v1**
(23 May 2019); numbering below follows v1. Copy of the paper: [paper.pdf](paper.pdf); note that this
copy is arXiv v3 (2024), *Topological Characterization of Consensus in Distributed Systems*. v3 extends
the paper to models with benign faults, and we formalized it as well (see the last section and the
v1 ↔ v3 table).

**Verdict: ⚠️ Weakened.** The core characterization (Theorem 5.5) is correct: under any message adversary, consensus is
solvable iff the admissible executions split into decision sets that are open (hence clopen) in the minimum topology
and contain the valent executions; its limit form (Corollary 5.18) holds too. But the paper's succinct characterizations
built on it are false: Corollary 5.6 ("no connected component contains two valences"), Theorem 5.11 ("every component is
broadcastable") and Theorem 6.7 (the non-compact case). For compact adversaries, Corollaries 6.1 and 6.5 are false as
well and the characterization by `ε`-approximations (Theorem 6.6) is unestablished.

## Mistakes in the paper

### ❌ Corollary 5.6, Theorem 5.11 and Theorem 6.7 ("if" direction)
On three processes, the message adversary `{π_k | k ≥ 1} ∪ {σ_∞}` has only broadcastable components and no
component with valent executions of two values, yet consensus is impossible (`V1Cex.v1_theorem_5_11_false`).

**Impact.** The paper's succinct characterizations built on Theorem 5.5 are false; Theorem 5.5 itself and the
"only if" directions stand. v3 repairs Theorem 5.11 by adding "the strong broadcaster decision sets are clopen"
(Theorem 7.9).

**Details.**
- *Model.* Three processes; message adversary `{π_k | k ≥ 1} ∪ {σ_∞}`.
  - `σ_∞` has `1→0` and `1→2` in every round.
  - `π_k` has no edges in rounds `1..k-1`, `2→0` in round `k`, and then `0→1`, `0→2` forever.
- *The conditions hold.*
  - The executions with pattern `π_k` fall into clopen sets, one per `(x₀, x₂, k)`. Inside each,
    nobody ever hears of process 1, and process 0 broadcasts.
  - The component of `(x, σ_∞)` is `{(y, σ_∞) | y₁ = x₁}`, and process 1 broadcasts there.
  - So every component is broadcastable, and no component contains valent executions of two
    different values.
- *Consensus is impossible.*
  - `((1,0,1), π_k)` must decide like `((1,1,1), π_k)`, because process 0 never hears of
    process 1. So it decides 1.
  - For large `k`, process 1 cannot distinguish `((1,0,1), π_k)` from `((0,0,0), σ_∞)` before
    it has to decide in the latter.
- *Why the proofs fail.* Theorem 5.11 "⇐" and the meta-procedure behind Corollary 5.6 assume that the union of
  the components of the `v`-valent executions is open. That holds only with finitely many components. Here the
  components `{(x, σ_∞)}` are not open.
- The adversary is not limit-closed, which is why it also refutes Theorem 6.7 (the non-compact case).

### ❌ Corollaries 6.1 and 6.5 (finitely many connected components, `ε`-approximations of components)
The limit-closed adversary `{σ_n} ∪ {σ_∞}` on two processes, with `σ_∞ = (1→0)^ω` and `σ_n` equal to `σ_∞` with
`0↔1` in round `n+1`, makes consensus solvable but has infinitely many components
(`CanonicalCex.v1_corollary_6_1_false`), and for every `ε > 0` the `ε`-approximation of `(y, σ_∞)` contains executions
`(x, σ_n)` from other components (`CanonicalCex.v1_corollary_6_5_false`).

**Impact.** Both statements are false, and nothing we proved recovers finiteness or a matching `ε`. This also
invalidates the proofs of Lemma 6.4 and Theorem 6.6 (next item).

**Details.** Every `(x, σ_n)` is its own component. The proof's "open covering" by components is not open.

### ❌ Lemma 6.4 and Theorem 6.6 (unestablished)
Theorem 6.6 is derived from Theorem 5.11 and Corollary 6.5, both false, and the proof of Lemma 6.4 rests on
Corollary 6.1 and on the step "setting `ε < d/2`", which gives no bound on the iteratively grown `PS^ε`, so the proofs
are invalid.

**Impact.** Statements unestablished: we did not settle them.

### ❌ Corollary 5.15 ("⇐")
The proof relies on the triangle inequality, which `d_min` does not satisfy.

**Impact.** Unestablished; v3 drops this direction. We did not formalize Corollary 5.15. A related Lean example
(`ClosureCounterexample.closure_not_setDistZero`) shows a point in the closure of a set at positive distance from
it.

### ⚠️ Theorem 5.9 and Corollary 5.10 (connected broadcastable sets)
The proof builds `U(a)` by asymmetric forward reachability and treats it as an equivalence class, so the needed
disjointness of `U(a)` and `V(a)` does not follow.

**Impact.** We prove the conclusion only in a weaker form: for message adversaries, every component of a solvable
adversary has a common broadcaster with constant input (`DN.dn_corollary_7_7`). No Lean theorem states Theorem 5.9
itself, for an arbitrary connected broadcastable set and a given broadcaster.

### ✏️ Slips
- *Lemma 4.7 (statement).* It allows any `d : X × X → {0,1}` and fails without reflexivity
  (`Lemma42Counterexample.lemma_4_2_false_without_refl`); every distance the paper applies it to is reflexive.
- *Corollary 5.18.* "Limit points in `PT^ω`" is ambiguous for these non-metric topologies; we state it in `Σ`.

## Proof gaps (statements true)

### 🛠️ Theorem 5.11 "⇒" (broadcastable components)
The proof does not show that its execution `c` lies in the needed component.

**Impact.** The statement is true for message adversaries: every component of a solvable adversary has a common
broadcaster with constant input (`DN.dn_corollary_7_7`).

**Repair.** A different argument: the first label flip along the inputs `1^k 0^{n-k}` under a fixed pattern gives the
broadcaster.

### 🔧 Lemma 4.7 (product topology, proof)
The proof claims that the balls `B_1(C)` are open, which fails when the zero-distance relation is not transitive,
as for `d_min` on configurations, where v1 applies the lemma (`BallCounterexample.ball_one_not_isOpen`).

**Impact.** The statement is true for reflexive 0/1 distances.

**Repair.** A chain argument (`lemma_4_2`): replace `B_1` by the set reachable through chains of zero-distance steps,
moving one coordinate at a time.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model (v1, `DynamicNetworks.lean`).**
* `n` lock-step synchronous, correct processes run a full-information protocol.
* An arbitrary message adversary `MA ⊆ (ℕ → Graph)` chooses the round graphs (CSLib
  `HeardOf.Graph` convention). It need not be limit-closed.
* All input assignments are admissible, independently of the pattern.
* The view of `p` is compared by `FIIndist`: recursive equality of full-information views,
  equivalent to equal process-time-graph views (the shared `Cslib.HeardOf.FIIndist` of
  `Cslib/Computability/Distributed/DynamicNetworks/FullInfo.lean` with initial views given by the inputs). The heard-of
  relation `Heard` is the shared journey relation (`Cslib.DynNet.Journey`), and the generic
  model's indistinguishability relations form a `Cslib.Knowledge.IndistSystem`.
* The minimum topology is `τU`, induced by `d_u = min_p d_p`. Decision sets are labellings `Σ → V`.
* This is an instance of the generic model of v3, `Model.lean`.

**Main results in Lean (v1 numbering).**

| v1 (PODC'19) | v3 | Status | Lean | File |
|---|---|---|---|---|
| Lemma 4.6 (distance-induced topology) | Lemma 4.1 | holds | `distTopology` | `Distance.lean` |
| Theorem 4.3 (`d_P` pseudometric) | Lemma 4.3 | holds | `Model.dP_self`, `dP_comm`, `dP_le_max` | `Distance.lean` |
| Lemma 4.7 (product topology) | Lemma 4.2 | holds with reflexivity; proof gap | `lemma_4_2`, `Lemma42Counterexample.*`, `BallCounterexample.*` | `ProductTopology.lean` |
| Lemma 5.2, Theorem 5.4 (decision maps continuous) | Lemmas 4.4/4.5 | holds | `Model.isOpen_fiber_τU`, `theorem_5_2_necessary` | `Characterization.lean` |
| **Theorem 5.5** (characterization) | Thm 5.2 (fault-free) | holds | `DN.dn_theorem_5_2`, `DN.dn_solvable_iff` | `DynamicNetworks.lean` |
| Corollary 5.6 | — (meta-procedure) | "if" false | `V1Cex.v1_theorem_5_11_false` | `V1Cex.lean` |
| Theorem 5.9 / Cor 5.10 (broadcastable components) | Lemma 7.6 | weaker form for MAs (proof gap) | `DN.dn_corollary_7_7` | `Broadcast.lean` |
| Theorem 5.11 | Theorem 7.9 (+ cond. (ii)) | "if" false; "only if" holds | `V1Cex.v1_theorem_5_11_false`, `DN.dn_corollary_7_7` | `V1Cex.lean`, `Broadcast.lean` |
| Lemma 5.17, Corollary 5.18 | Lemma 6.3, Thm 6.4 | holds (in `Σ`) | `lemma_6_3`, `Model.theorem_6_4_uniform_faultFree` | `Limits.lean` |
| Cor 5.15, Def 5.16, Cor 5.19 | Lemma 6.2, Def 6.6, Cor 6.7 | not formalized | — | — |
| §6.1 lossy link `{←,↔,→}` / `{←,→}` | §8.1 | holds | `LossyLink.not_solvable_MA3`, `LossyLink.solvable_MA2` | `LossyLink.lean` |
| Corollary 6.1 | Corollary 8.3 | false (finitely many components) | `CanonicalCex.v1_corollary_6_1_false` | `V1Cex.lean` |
| Corollary 6.5 | Corollary 8.7 | false | `CanonicalCex.v1_corollary_6_5_false` | `V1Cex.lean` |
| Lemma 6.4, Theorem 6.6 | Lemma 8.6, Thm 8.8 | proofs invalid, statements open | — | — |
| Theorem 6.7 | Corollary 8.2 | "if" false | `V1Cex.v1_theorem_5_11_false` (adversary is not limit-closed) | `V1Cex.lean` |

**Not formalized.** Corollary 5.15 and fair/unfair sequences (Definition 5.16, Corollary 5.19);
Lemma 6.8; the statements of Lemma 6.4 and Theorem 6.6.

**Trust.** No `sorry`. Every theorem named in this README uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. For non-vacuity, the characterization is exercised in both
directions: `{←,→}` is solvable via the universal algorithm, and `{←,↔,→}` is unsolvable through a
forever-bivalent limit. Both counterexample adversaries are concrete.

## Errors in the 2024 extension (arXiv v3 only)

v3 generalizes v1 to a generic model with obedient/disobedient processes and weak clocks. Its new
statements contain further errors, all formalized:

1. **Theorem 5.2 "if" (uniform topology `d_u`) is false.**
   - *Background.* `d_u` only counts processes obedient in both executions, which misses faulty
     processes that cannot detect their own fault.
   - *Counterexample.* Two non-communicating processes; process 0 is faulty from round 1 in the
     mixed execution. (`CexUniform.theorem_5_2_false`)
   - *Fix.* The asymmetric distance `d_uc`. (`Model.theorem_5_2c`)
   - *Same error.* Section 8.2's computation `d_u(α, α₀) = 0` contradicts the definition of `d_p`.
2. **Theorems 5.2/5.3 "if" are false in the generic weak-clock model.**
   - *Counterexample.* Global time is hidden; executions differ only by a time shift.
     (`CexAsync.theorem_5_3_false_async`)
   - *Fix.* We add `LockstepRecall`: views determine the global time and earlier views. With it,
     Theorem 5.3 is proved. (`Model.theorem_5_3`)
3. **Theorem 7.9 / Corollaries 8.2, 8.3 are false with the canonical (smallest common)
   broadcaster.**
   - *Counterexample.* A limit-closed adversary where a canonical broadcaster decision set is not
     closed. (`CanonicalCex.theorem_7_9_canonical_false`)
   - *What holds.* With an existentially chosen broadcaster the claim is true for message
     adversaries. (`DN.dn_theorem_7_9_exists`)
4. **Lemma 8.6 / Corollary 8.7 are false.** (`CanonicalCex.corollary_8_7_false`)

Also proved for v3:
* Theorem 5.3 under `LockstepRecall`;
* the strong-validity version of Theorem 5.2 (`Model.theorem_5_2c_strong`);
* Theorem 7.12 (1)⇔(3)⇔(4) for message adversaries (`DN.binary_iff_strong`, `DN.binary_iff_weak`);
* Theorem 6.4 and Corollary 6.5 (`Limits.lean`).
