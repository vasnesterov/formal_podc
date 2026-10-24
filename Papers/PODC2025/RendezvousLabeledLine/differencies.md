# Differences between the formalization and the paper

Paper: Bourreau, Narayanan, Nolin, *Optimal Deterministic Rendezvous in Labeled Lines*,
arXiv 2505.04564v2.

## Model

1. **Frame model instead of port numbers.** An algorithm is a causal trajectory in the agent's own
   frame (`Algo`): `pos μ t`, where `μ i` is the label at frame position `i`. Causality says the
   move in round `t+1` depends only on the labels of the nodes visited by round `t`. The adversary
   chooses each agent's frame orientation `ε = ±1`. Port numbers at nodes other than the start
   carry no information that our algorithms use. Every frame algorithm is implementable with ports,
   since an agent knows its entry port and can keep its direction. Frame algorithms form a
   subclass, so upper bounds transfer to the paper's model. The simulation "frame algorithm → port
   algorithm" itself is not formalized.
2. **Labels** are an injective `ℓ : ℤ → ℕ` (the paper uses `ℕ*`); `0` is allowed.
3. **`log*`.** `lstar n = Nat.logStar n + 1`, where `Nat.logStar` iterates `⌊log₂⌋`. The paper uses
   the real `log`, with `log* x = 1` for `x ≤ 1`. The two differ by an additive constant, which is
   absorbed in the constants. The levels of Algorithm 3 are `V_i = {v | lstar (ℓ v) = i}`, and
   labels in `V_i` are `< tower i`.
4. **Wake-up.** The first agent `α` wakes up in round 0 and `β` in round `τ`. Rounds are counted
   from `α`'s wake-up. The theorems hold for every `τ` and every assignment of the two start nodes,
   which covers either agent waking up first.
5. **ES-LOCAL** is modelled extensionally. "Node `v` commits within `T` rounds" means "its output is
   a function of the labels within distance `T` of `v`" (`IsLocal`), with `T` depending on `ℓ(v)`
   for early stopping. Lemma 3.5 (3), the statement about the sets `S_T` committed by round `T`, is
   represented by `ColRuling.knows` / `knows_exists`. We do not state it for every `T`.
6. **Equivariance.** The ruling-set rule must commute with the isometries of `ℤ` (`inS_frame`,
   `col_frame`). This is implicit in the paper: algorithms run on the unoriented labelled line, and
   both agents must simulate the same ruling set from views read in different frames.

## Statements

7. **Theorem 1.1.** We prove: for every node `u₀` within distance `D` of `vα` or `vβ`, rendezvous at a
   node happens by round `4 · (896·40001 + 14336) · D · log* ℓ(u₀)` (`thm_1_1_final`). This is the
   same as using `ℓ_min` over `N^D(vα) ∪ N^D(vβ)`, the definition used in Lemma 4.4. The theorem says
   "within distance `O(D)`". For `D = 0` the bound is `0`.
8. **Theorem 1.1, parametric form.** `thm_1_1` holds for an arbitrary `ColRuling κ` with constant
   `4(896κ + 14336)`. `ES.rule` has `κ = 40001`.
9. **Theorem 3.1** is proved in two forms. The first is for trajectories in any type of nodes with
   injective labels (`care_meet`, the paper's "labelled graph"). The second is for agent algorithms
   on the line (`thm_3_1`). The bound is the same (`4T`). The delay for `A` is `⌈τ/4⌉`, as in the
   proof.
10. **Proposition 3.2 (2)** is proved as stated. Internally we use the endpoint form
    (`prop_3_2_scan'`): only visits of `a` and `d` are needed.
11. **Proposition 4.1** is definitional in our closed-form definition of Algorithm 5
    (`iterStart k = 28(2^k-1)`). `prop_4_1` records it, together with "the agent is at its start at
    the beginning of every iteration". The fact that SearchingWalk lasts exactly `24L` rounds and
    ends at the start is `sw_end`.
12. **Lemma 4.3.** `L = 2^(⌈log₂ D⌉+1)`. We prove the dichotomy: `2τ < 5L ≤ 20D`, or a meeting or
    crossing occurs in rounds `[0, T_{α,L} + 3L]`.
13. **Lemmas 4.5–4.7** assume `τ < 10D`, which is what the paper's proofs use after "otherwise
    Lemma 4.3". Lemma 4.5 states `⊥` as `R = 0` (`rOf`) and gives `T_{α,L} + 8L`, not `7L` (see the
    README). Lemma 4.6 gives `T_{α,L} + 5L` as in the paper. Lemma 4.7 gives `T_{α,L} + 28L` as in
    the paper.
14. **Lemma 4.4** is stated for one agent, for any `u₀` within `2D` of its start, with
    `L ≥ 8κ D log* ℓ(u₀) + 128 D` a power of two. The conclusion is `R* ≥ 2D`.
15. **Lemma 3.4.** Correctness (`lemma_3_4`): a `U`-limited `(R, R-1)`-ruling set when labels on `U`
    are `< n`. Complexity (`lemma_3_4_isLocal`): `ρ_U + 3R(log* n + 267)` rounds, where `ρ_U` is the
    cost of knowing `U`.
16. **Lemma 3.5** is formalized as the structure `ColRuling κ` and its instance `ES.rule`. Fields:
    * packing `≥ R`;
    * ruling-set nodes known within `R-1` (`knows`);
    * colours in `[17]`, proper on `G^{9R-1}[S]`;
    * commitment within `κ R log* ℓ(u)`, with `κ = 40001`.

    The ruling-set property of the final `S` is the same as in the paper. Item (2) is weakened as
    explained in the README: `u` knows the members of its own or lower levels.
17. **Lemma 2.1** (cited from Linial) is proved for the graphs used, with explicit constants. The
    graphs are `G^k[S]` for `S ⊆ ℤ` with labels `< n`, and the degree bound is supplied by packing.
    * Colouring: `log* n + 3` rounds of `G^k[S]` with Linial's reduction (CSLib), giving
      `< max(16Δ², 256)` colours (`colRule`).
    * MIS for degree `2`: a further `256` rounds (`misRule`).

    The general `degree+1`-list colouring is not formalized. It is replaced by the sweep described
    in item 19.

## Algorithms

18. **Algorithm 2.** As in the paper, but the distance `b_v` to `S_out` is truncated at `M = 3R`
    (`tdist`). This changes nothing, since every candidate is within `3R-3` of `S_d`, and it keeps
    the rule local even on inputs where the hypotheses fail. The MIS radii `R_i` (`prsRad`) and the
    6 greedy iterations are the paper's.
19. **Algorithm 3, membership.** As in the paper (lines 3, 5–6, 7–9), with truncation `M = 2R` and 4
    greedy iterations. The explicit "wait `Θ(R·i)` rounds" of line 4 disappears in the extensional
    model: membership of level `i` depends on the outputs of lower levels within distance `R`,
    which are decided after `816 R (i-1)` rounds.
20. **Algorithm 3, colouring (changed).** Lines 10–11 are replaced. The new nodes `N_i` of level `i`
    first get Linial classes on `G^{9R-1}[N_i]` (degree `≤ 16`, `4096` classes), which needs no
    colours of lower levels. Then the classes are swept: a node of class `c` takes the least colour
    in `[17]` unused by ruling-set nodes of lower levels and of classes `< c` within distance
    `9R-1` (at most 16 such nodes). This repairs the complexity gap of Lemma 3.5. As in the paper,
    the result is proper on `G^{9R-1}[S]` with 17 colours.
21. **Algorithm 5.** The searching phase of iteration `L` uses `R*` as in lines 4–6, with closed
    balls. The agent knows a ruling-set node `w` when some `u ∈ S_{R*}` knows `w` in the sense of
    `ColRuling.knows`. Line 8's `r` is the known node closest to the start, ties broken by labels
    (`rsel`). The colour `χ(r) ∈ [17]` is read in binary over 5 bits.
22. **Algorithm 6.** As in the paper. In the bit phase, bit `i` occupies rounds
    `[L + 32R + 64Ri, L + 32R + 64R(i+1)]` of SearchingWalk.
23. **Algorithm 1 (CarefulWalk).** A move `u → v` occupies 4 rounds with positions
    `u, u, v, (v if ID(v) > ID(u) else u)`, then `v` at the start of the next block, exactly as in
    the paper.

## Proofs

24. **Lemma 3.4, greedy covering.** We choose `w` differently: it maximizes `(b, ℓ)` among the
    candidates in the same gap of `S_out` and within distance `B` of `v`. The count is also
    different: at most 2 added nodes per side, so 5 iterations suffice (the paper argues with 6
    nodes and 6 iterations, which is off by one).
25. **Lemma 3.5, complexity.** This is a new proof, by induction on levels with explicit radii
    `816 R i` (membership) and `40000 R i` (colours). The paper's recurrence argument is invalid
    (`lemma_3_5_recurrence_gap`).
26. **Lemma 4.5.** The `ZWalk(8R)` window is `[T+5L, T+5L+32R]`, not `[T+5L, T+6L]`. The sweep of the
    larger-`R` agent is used between its rounds `8R` and `24R` of the ZWalk.
27. **Lemma 4.7.** Any differing bit is used. If `α` has bit 1, its *second* `ZWalk` of that bit is
    used; if `β` has bit 1, its *first* one is used. This makes `τ < 10R ≤ 32R` suffice.
28. **Not formalized.**
    * Corollary 1.2 and Remark 5.1 (finite graphs).
    * The Miller–Pelc lower bound behind "optimal".
    * The general-graph port model of Section 2.2: only the line is formalized, apart from
      `care_meet`.
