# Differences between the formalization and the paper

Paper: Altisen, Devismes, Durand, Johnen, Petit, *Self-stabilizing Systems in Spite of High Dynamics*.
PODC 2020 brief announcement (DOI 10.1145/3382734.3404502, no proofs); formalized from the full version
(Theoretical Computer Science 2023, author manuscript HAL hal-04109662, 48 pp.). Numbering follows the full
version.

## Mistakes and imprecisions in the paper (with labels)

- ✏️ **Corollary 1 is stated too strongly.** It says that if a set `L` of legitimate configurations for `V` is closed in
  `TC_B(Δ)`, then `A` "should not be size-ambiguous". The paper calls it the contrapositive of Theorem 1, which only
  gives "`A` is not `(k, V)`-ambiguous" for this `V`. The printed version is false. Algorithm 1 is size-ambiguous, yet
  for a single process its quasi-legitimate configurations form a closed set of legitimate configurations
  (`corollary_1_as_stated_false`, `alg1_singleton_closed`). We prove the contrapositive (`corollary_1`). Theorem 3
  is unaffected: it applies Corollary 1 to every `V`.
- ✏️ **Theorem 6, Corollary 8, Lemma 13, Corollary 9: two implied assumptions.** The proof swaps the leader `p_ℓ` for a
  fresh process `v ∉ V` and keeps the states of the other processes.
  1. It needs `|IDSET| > n`. With `IDSET = Fin 2`, the algorithm `knowsN2` (input `n`; `lid := 0` if `n = 2`,
     `lid := id(p)` if `n = 1`) is pseudo-stabilizing (`knowsN2_pseudoStab`), `SizeOnly`, and correct from round 0
     for `n = 2` (`theorem_6_needs_large_IDSET`). We assume `[Infinite ι]`.
  2. It needs the possible local states of a process to depend on the system only through `|V|` (`SizeOnly`).
     Otherwise the states of `V \ {p_ℓ}` need not be states of the new system. If the processes know `V` (state =
     `V`, `lid := min V`), the algorithm is pseudo-stabilizing and every execution is correct from round 0 (`knowsV`,
     `knowsV_pseudoStab`, `theorem_6_needs_sizeOnly`). The paper's
     algorithms know at most `n` and `Δ`, so this is an implied assumption of the model.
- Algorithm 3, line 7: `insert(p, ⟨id(0), 0⟩)` is a typo for `insert(p, ⟨id(p), 0⟩)`.
- Lemma 11, proof case 2: "edge `(r, p)`" should be "edge `(r, q)`".
- Section 3.3, before Corollary 1: "the set of legitimate configurations of Algorithm 1 is not closed" holds only for
  systems of at least two processes (`alg1_not_closed`). For one process it fails (`alg1_singleton_closed`).

## Proof gaps (statements true)

- 🔧 **Lemma 6 (Algorithm 2).** The proof says that after `id` is pushed, evicting it requires inserting `n` distinct
  identifiers not in `members(p)`. This is false: re-inserting identifiers ahead of `id` (lines i2–i3) moves them behind
  it (`Alg2.lemma_6_counting_claim_false`: with `n = 3`, one new identifier evicts `5` from `[1, 2, 5]`). The lemma is
  true. From round `Δ + 1` on, the longest suffix of the queue whose identifiers are all real only grows, and none of
  its elements is evicted: if the head is in it, the queue is all of `V` (`n` distinct real identifiers), so no absent
  identifier is inserted (`Alg2.lemma_6_suffix`, `Alg2.lemma_6`). The proof also uses, without stating them, that
  `n = |V|`, that the identifiers in the queue are distinct and that the queue has at most `n` elements. All three hold
  in configurations of Algorithm 2 for `V`. Lemma 6 is stated as: if `t ≥ Δ` and `q = p` or some in-neighbour of `p`
  sends a pair `⟨q, _⟩` in round `t + 1`, then `q ∈ members(p)` at the end of every later round.

- 🔧 **Lemma 11 (Algorithm 3).** "`id(p)` cannot be removed from `members(q)` … by Lemma 10" and "this pair is not
  rejected" need a counting step that the proof leaves out. The max-timestamp entry with timestamp `≤ i − 2` is evicted
  at line i6 only if every entry has timestamp `≤ i − 2`. Then, by Lemma 10, all keys are real. The map is full, so its
  keys are exactly `V`, and no absent identifier can arrive. This must hold at every intermediate state of the line 4–5
  loop, for every processing order and tie-break of `max(p)`, and also at line 7, which the proof does not discuss.
  Repaired in `Alg3/Round.lean` (`mem_keys_of_full_lt`) and `Alg3.lemma_11`.
- Theorem 2: the proof shows only that its set `L` is closed and correct. Convergence of `L` is not mentioned. It follows
  because every legitimate set of `A` is contained in `L`. Proved in `theorem_2`.
- Lemma 9 (Algorithm 2) and the proof of Theorem 8 (Algorithm 3): "`members` has at most `n` entries, hence it is
  exactly `V`" uses that the identifiers are distinct and that `n = |V|`; both come from the configuration invariant.
- Lemmas 3 and 4 (Algorithm 1): the steps "`lid(p)` stays `id(ℓ)`" and "no process can reset" also use that every
  received identifier is `≥ id(ℓ)`, i.e. quasi-legitimacy (Lemma 2). The proofs do not cite it. Trivial.

## Modelling choices

- **Processes = identifiers.** `ι` is `IDSET`, with a linear order. A system is a finite `V : Finset ι`, nonempty
  (`SP_LE` cannot hold for `V = ∅`; the paper implicitly has `n ≥ 1`).
- **TVGs.** A TVG is a dynamic graph `G : ℕ → Graph ι` with `IsDG V G` (loopless, edges inside `V`). The static arc set
  `E` and the lifetime are implicit. Rounds are 0-indexed: `G t` is the snapshot of the paper's Round `t + 1`, and
  `exec G γ t` is `γ_t`, the configuration at the end of Round `t`. `TC_B(Δ)`, `TC_Q(Δ)`, `TC_R` are the all-pairs
  classes `JssB`, `JssQ`, `Jss` of the PODC 2021 formalization (`Papers/PODC2021/StabilizingLEDynamic`). They are
  defined by temporal distance (`tdist`, journeys with strictly increasing times). The paper's `d̂_{p,t}(q)` with
  departure `> t` is `tdist G (t − o_T + 1) p q`. In particular `d̂_{p,o_T}(q) = tdist G 1 p q`.
- **Algorithms (`SAlg`).** The algorithm is defined for every set of processes. The code of process `p` (one
  synchronous round, as a function of its state and the states received) does not depend on `V`. Knowledge such as `n`
  is an input stored in the state, so it is captured by the sets `S V p` of possible local states, exactly as in the
  paper's discussion before Definition 3. This makes the code-independence used in the proofs of Theorems 1 and 6
  explicit. Algorithms are full-information: a process receives the whole state of each current in-neighbour and
  knows who sent it. This is at least as strong as the paper's `SEND` of part of the state, so the impossibilities
  are not weakened. The algorithms of Sections 4–6 only use the parts they send.
- **Definitions 1, 2, 6** are stated for recurring classes in the form of Remarks 1 and 2 (executions from time 0 of
  every graph of the class). All classes used are recurring (`J_shift`).
- **Stabilization time** "at most `T`" is stated as "every execution is in the legitimate set from round `T` on"
  (Corollaries 5/6, Theorems 7, 9). Unboundedness (Corollaries 8, 9) is stated as "there is no `f` such that, for every
  `V` of size `n`, *some* legitimate set is reached within `f(n, Δ)` rounds by every execution". This is the strongest
  form of the negation.
- **Theorem 2** assumes that executions stay in the configurations of `A` for `V` (`Invariant`). The paper builds this
  into the definition of an execution. Theorem 3 and Corollary 3 are proved without this assumption: they apply the
  core of Theorem 1 directly to the set `L` of the proof of Theorem 2.
- **Theorem 1** is proved with a simpler TVG than the paper's. It is the complete graph on a `k`-subset `U` not
  containing the leader in even rounds and the complete graph on `V` in odd rounds; the rotating window is not
  needed. The paper's configurations `γ^i` are exactly the execution in the static complete graph on `U`.
- **Theorem 6, Lemma 13** do not assume the algorithm pseudo-stabilizing (a bound would imply it). They take the extra
  assumptions `[Infinite ι]` and `SizeOnly A` (see above).
- **Statement forms.** Lemma 3 (Algorithm 1) is proved by induction on the length of a journey from `ℓ` instead of
  the paper's double induction on `(d, j)`. Lemma 4 also covers `r = 0`. Lemma 7 is stated with any `j ≥ Δ` such
  that `tdist G j q p ≤ Δ`, instead of the minimal `t(q, p)`. Several lemmas need fewer hypotheses than in the paper
  (for example, Lemmas 1, 5 and 10 hold from any configuration). `Δ ≥ 1` is assumed where the paper has `Δ ∈ ℕ*`.
- **Algorithm 1.** The state is `⟨lid, ttl⟩` with `ttl < 2Δ` (`S V p`, independent of `V`). Line 7's lexicographic
  minimum is `lexMin`.
- **Algorithms 2 and 3.** The state is `⟨n, members, lid⟩`, with `members` a list of pairs. In Algorithm 2 it is the
  FIFO queue, head first. In Algorithm 3 it is a map, with the insertion order irrelevant. `S V p` requires `n = |V|`,
  at most `n` entries with distinct identifiers, and, for Algorithm 2, timestamps `≤ Δ`. The received pairs are
  processed in the order of `Finset.toList`, which is arbitrary, and all round lemmas are proved for every list (any
  order, duplicates allowed). Algorithm 3's `max(p)` breaks ties by `List.argmax`; the proofs only use maximality.
  Algorithm 3's line 7 uses `id(p)` (typo fixed). For Algorithm 2's queue, distinct identifiers are our reading of the
  paper's notation `members(p)[id]` (the variable declaration only says "queue of at most `n` elements"); for
  Algorithm 3's map they are part of the notion of a map.
- **Processing order.** The algorithms `Alg2.alg` and `Alg3.alg` fix one order of the received pairs (that of
  `Finset.toList`, with each distinct pair once). The execution-level theorems are stated for this algorithm, but
  their proofs only use the round lemmas, which hold for every list of received pairs.
- **Complexity claims** (memory and message sizes in Corollary 6, Theorem 5) are not formalized.
- **Remark 4 / Remark 5** (other problems, counting `n`) are not formalized.
