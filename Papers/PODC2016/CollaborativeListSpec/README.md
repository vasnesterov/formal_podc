# Specification and Space Complexity of Collaborative Text Editing — PODC 2016

Hagit Attiya, Sebastian Burckhardt, Alexey Gotsman, Adam Morrison, Hongseok Yang, Marek Zawirski.
*Specification and Complexity of Collaborative Text Editing.* PODC 2016. DOI
[10.1145/2933057.2933090](https://doi.org/10.1145/2933057.2933090). Formalized version: the journal
version *Specification and space complexity of collaborative text editing*, TCS 855 (2021) 141–160,
which has complete proofs. Lean docstrings use the TCS numbering. The verdict judges the PODC 2016
paper (and its extended version with appendices); we checked that its RGA pseudocode, Definitions 1–13
and the lower-bound construction are the same as in the TCS version. Numbering map (PODC → TCS):
Theorem 1 → 1 (PODC claims only the strong list specification; TCS adds eventual visibility),
Lemma 3 → Lemma 6, appendix Lemmas 13–16 → Lemmas 3, 4, 5, 7, Theorems 4–5 → Theorems 8–9,
Claims 6–9 → Claims 10–13.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main result holds. Any push-based protocol with at
least three replicas that satisfies the weak list specification has metadata overhead Ω(D)
(PODC Theorems 4 and 5). We formalized the encoding/decoding proof completely and found only small
gaps. Theorem 1 (RGA implements the strong list specification) fails for the protocol as literally
written, because its insert procedure counts tombstones when it locates the insertion position. The
fix is a local index change that the paper's own definition of `ins(a, k)` dictates; with it,
Theorem 1 holds.

## Mistakes in the paper

### ⚠️ Theorem 1 (RGA of Section 4.2 implements the strong list specification)
RGA as written violates condition (1c), because its insert locates the parent in `s(N)`, which still contains
tombstones: at one replica, `ins(x,0); ins(y,1); del(x); ins(b,1)` returns `b y`, while (1c) requires `b` at
position 1 (`RGA.literal_not_weak`, `RGA.literal_not_satisfies`).

**Impact.** A local index fix that the paper's own definition of `ins(a, k)` dictates; with it Theorem 1 holds
(`RGA.theorem1_strong`). Borderline: without R3 this would be a false claim about the paper's own algorithm.

**Details.** The RGA `do` transition builds the new node "as described in the Insert procedure of Section 4.1".
That procedure takes the parent `p = a_{k−1}` of `s(N) = a₀ … a_{n−1}`, a list that still contains the deleted
(tombstoned) elements. However, `ins(a, k)` and condition (1c) count positions in the user-visible list
`s(N) \ T`. In the example, before the last insert, `s(N) = x y` and the visible list is `y`. The parent of `b` is
`a₀ = x`, so `s(N) = x b y` and the response is `b y`. But (1c) requires `b` at position `min(1, 1) = 1`. No
abstract execution of this execution is in `A_weak`, let alone `A_strong`. The proof says only that "(1c) follows
directly from the properties of the TI data structure". The same counterexample works with any number of
replicas.

Why ⚠️: the fix is local, the same tree rule applied to the list the user sees. The intent is recoverable from the
paper: Section 3 defines positions on the returned list, and Insert's prose says "the element to the left of the
insertion position". The proof never reasons with the tombstone-counting index. So R3 applies.

**Repair.** Take the parent in the visible list, `p = w_{min(k,|w|)−1}` with `w = s(N) \ T`. This is what the
original RGA does, and it is what the meaning of `ins(a, k)` in Section 3 requires. With this fix we proved
Theorem 1 (`RGA.theorem1_strong`).

### ⚠️ Definition 10, eventual visibility (TCS version only)
Definition 10 lacks the network-connectivity assumption, so the TCS claim that RGA guarantees eventual visibility
fails when replica 0 runs `ins(a,0)` and never sends its message while replica 1 reads forever
(`RGA.def10_needs_connectivity`).

**Impact.** Does not affect the verdict: PODC 2016 does not claim eventual visibility. An implied assumption (R4):
no protocol can do better, and under Definition 1 the claim holds (`RGA.theorem1_eventualVisibility`).

**Details.** Definition 10 asks that *every* execution with causal broadcast comply with an abstract execution
satisfying eventual visibility. In the counterexample every read returns `[]`, so by (1a) the insertion is visible
to none of them, and no abstract execution in `A_weak` satisfies eventual visibility. The connectivity assumption
is evidently intended: the remark after Definition 10 says so, and the proof of Theorem 1 relies on it.

### Typos and slips
- Section 4.1 is inconsistent about how a node names its parent. PODC 2016 declares `p ∈ C ∪ {◦}` (the parent's
  timestamp, with `n′.p = n.t`, as in the node `(b, t_b, t_a)` in the proof of appendix Lemma 15). Fig. 2 and the
  Insert procedure (`p = a_{k−1}`) instead name the parent by its element. The TCS version switches the
  declaration to `p ∈ U ∪ {◦}` but keeps `n′.p = n.t` and `(b, t_b, t_a)`. We name parents by their element.

## Proof gaps (statements true)

### 🛠️ Theorem 9 (PODC Theorem 5, the lower bound)
The proof has three small gaps: Claim 12 (PODC Claim 8) asserts an adjacency the weak specification does not give,
the choice of `σ_w` after the final read breaks the counting of internal states, and the constructed executions are
not checked against the user assumptions.

**Impact.** Statement true; all three repaired (`recover_correct`, `alpha_ok`).

**Details.**
- Claim 12 (PODC Claim 8) says that `R₂`'s read returns `…[ᵢ₋₁ ]ᵢ₋₁…` with the two brackets *adjacent*, because
  `R₂` must be able to insert `x` "between" them. The weak specification alone gives only the set of elements.
  Adjacency follows because `lo` orders the read's response and also `R₁`'s response at `ins ]ᵢ₋₁`, which has the
  same elements, and `lo` is transitive on the read's response. We prove the read returns exactly `R₁`'s list
  (`recover_correct`, step `hv`).
- In the general model a `read` may change the state, including the send buffer. The paper takes `σ_w` to be
  `R₁`'s state *after* the final read. Distinct pairs `(q, m)` then need not have distinct internal states `q`. We
  take `σ_w` *before* the read, right after `send(m_{d+3})`, so its buffer is empty and its user-visible content is
  `[∗]`. The read only witnesses this content.
- The proof does not check that the constructed executions obey the user assumptions, in particular that
  deletions only delete visible elements. The protocol is only required to be correct on such executions. We
  verify this by induction along `α_w` (`alpha_ok`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing, with no failures and no randomness (Section 2). A replica is a
  deterministic state machine. Its state is `(q, buf)` with a one-slot send buffer. A `do(op, v)`
  event is always enabled; its response is a function of the whole state `(q, buf)`, and it may
  change the whole state. A `send` moves to `(q′, ⊥)` where `q′ = sendStep r (q, buf)` is
  arbitrary. This is exactly the protocol class of PODC 2016 (the TCS version is narrower: responses
  depend on `q` only and sends keep `q`), so Theorems 8–9 cover every protocol of either version. A
  `send` broadcasts the buffered message to every replica, the sender included, and empties the
  buffer. A `receive` is always enabled. All replicas use one common type `Q`.
* An execution is a list of actions (an infinite sequence `ℕ → Act` for eventual visibility). A
  receive names the position of the send whose message it delivers; this makes messages unique, as
  the paper assumes. `HB` is Lamport's happens-before on positions. We formalize causal broadcast
  (Def. 2) and causal atomic broadcast (Def. 3), and sufficient connectivity (Def. 1) for infinite
  executions.
* An abstract execution is a visibility relation `vis` on the positions of the `do` events. It must
  contain the replica order and be transitive and irreflexive (Def. 4). The execution and its
  abstract execution share event ids, so compliance (Def. 5) is built in. We drop the linearization
  `H`: on the hypothesis side this only weakens the hypothesis, and for RGA we show `vis ⊆ <`.
* The user assumptions of Section 3 (`UserOK`): inserted elements are unique, and `del(a)` only
  deletes an element returned by the replica's previous operation.
* *Lower bound.* `PushBased P S Adm` is Def. 13, relative to a class `Adm` of executions.
  Theorem 9 assumes push-based only on executions with causal *atomic* broadcast that respect the
  user assumptions. This hypothesis is weaker than the paper's, so the theorem is stronger;
  `theorem9_causal` is the paper's form. The list universe is infinite. The size of an internal
  state is the length of its code under an *arbitrary* injective encoding `Q → List Bool`.
* *RGA.* TI trees are duplicate-free lists of nodes `(a, (x, i), parent)`. `s` is the paper's DFS
  (children in decreasing timestamp order). A replica's state is `(N, T)` plus a buffer `(A, K)`,
  and the new node's parent is taken in the *visible* list (see above).

**Main results in Lean** (namespace `Podc.CollaborativeListSpec`).

| Paper | Lean | File |
|---|---|---|
| Theorem 9 = PODC Thm 5 (any replica `R₁`, `D ≥ 4`: execution with `D` deletions, causal atomic broadcast, state of `R₁` with content `[∗]` and `≥ ⌊(D−2)/2⌋` bits) | `theorem9`, `theorem9_causal` | `Theorem9.lean` |
| Theorem 8 = PODC Thm 4 (worst-case metadata overhead `Ω(D)`) | `theorem8` | `Theorem9.lean` |
| Encoding `α_w` is admitted, well formed; `R₁`'s lists | `Params.alpha_ok`, `Params.rval_insert_phase`, `Params.alpha_read` | `LBAlpha.lean`, `Theorem9.lean` |
| Claims 10, 11 = PODC 6, 7 (`β_w^i`, `γ_w^i` well formed, causal atomic broadcast) | `Params.gamma_ok`, `Params.causalAtomic_γ` | `LBGammaWF.lean` |
| Claims 12, 13 = PODC 8, 9, and correctness of `Recover` | `Params.recover_correct` | `LBRecover.lean` |
| Decoding (`σ_w` determines `w`) | `Params.state_determines_bits`, `Params.y_congr` | `LowerBound.lean` |
| Counting step (`2^d` distinct states ⇒ one has `≥ d` bits) | `exists_long_code` | `Theorem9.lean` |
| Theorem 1 (strong spec, finite executions; vis = hb, so RGA is push-based) | `RGA.theorem1_strong`, `RGA.pushBased`, `RGA.satisfies_strong` | `RGA.lean` |
| Theorem 1, TCS only (infinite executions, eventual visibility under Def. 1) | `RGA.theorem1_inf`, `RGA.theorem1_strong_inf`, `RGA.theorem1_eventualVisibility` | `RGALive.lean` |
| Lemmas 3, 4 = PODC 13, 14 (state = visible updates) | `RGA.inv` | `RGA.lean` |
| Lemma 5 = PODC 15 (replica trees are TI trees) | `RGA.isTITree_Nall`, `RGA.isTITree_st` | `RGA.lean` |
| Lemma 6 = PODC 3 (`A ⊆ B` ⇒ `s(A)` subsequence of `s(B)`) | `s_sublist` (with `s_cons_max`) | `TITree.lean` |
| Lemma 7 = PODC 16 (list order total) | inside `RGA.strong` (order = subsequence of `s(N_all)`) | `RGA.lean` |
| `A_strong ⊆ A_weak` | `Strong.weak` | `Spec.lean` |
| Literal RGA violates (1c) | `RGA.literal_not_weak`, `RGA.literal_not_satisfies` | `RGALiteral.lean` |
| Def. 10 without connectivity fails for RGA | `RGA.def10_needs_connectivity` | `RGALive.lean` |

**Not formalized.** Theorem 2, the `O(D lg k)` upper bound for RGA, which is a size estimate.
Section 6.1 (client/server simulation, Proposition 14, Corollary 15). Section 7 (Theorem 16:
invisible reads plus eventual visibility imply push-based; Corollary 17).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity checks:
* RGA satisfies the hypotheses of Theorem 9 (`rga_pushBased_weak`, `rga_lowerBound` in
  `NonVacuity.lean`), so the lower bound applies to RGA.
* `RGA.connectedExec` is a sufficiently connected execution with an update.

The model is paper-local; `Model.lean` (generic replicated objects) is a CSLib candidate.
