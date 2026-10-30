# Differences between the formalization and the paper

Paper: Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, arXiv:1301.7119v2.
Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Model and modelling choices

1. **Embedding.** The paper embeds the graph in `ℝ³` with pairwise disjoint edge segments. We use the
   embedding `v ↦ e_v` into `V → ℝ` (`emb`, `point`, `posR` in `Model.lean`). Any embedding with pairwise
   disjoint segments gives the same meeting relation, so the meeting notion is identical.
2. **Walks.** `Walk` is the paper's walk written with a progress function. There are times `τ 0 = 0 < τ 1 < …`
   (the paper's `t_i`). `p` is continuous on each `[τ i, τ (i+1)]`, takes values in `[i, i+1]` there, and
   `p(τ i) = i`. The paper's `f_i(t)` is the point at fraction `p(t) - i` of the `i`-th edge. We do not
   require `τ i → ∞`: accumulating times are allowed, as in the paper, and a meeting must happen at a time
   when both positions are defined (`Meet`).
3. **Exploration procedure (UXS "axiom").** Reingold's procedure `R(k, ·)` is replaced by a hypothesis. For the
   rendezvous analysis it is `Explorer G P`: trajectories `R(k, v)` from `v`, walks of exactly `P(k)` edges,
   covering all edges if `|G| ≤ k`. They may depend on the whole graph, so this is more general than a
   port-local procedure. `Explorer.ofProc` / `theorem_3_1_ports` instantiate it with deterministic port-local
   procedures (`Proc`), assuming they traverse all edges of graphs of size `≤ k` (`TraversesUpTo`). For
   Lemma 2.1 the hypothesis is the paper's: the procedure visits all nodes of all graphs of size `≤ 2m`
   (`ExploresUpTo`). The "visit all neighbours" transformation of §2 is not formalized; it is subsumed by the
   hypothesis.
4. **Assumptions on `P`.** We assume `P(k) ≥ 1` (field `Explorer.P_pos`) and `P` non-decreasing. The paper
   states monotonicity only at the very end of the proof of Theorem 3.1, but uses it in Lemmas 3.2–3.6 and in
   Theorem 3.1, which compare `|A(·)|`, `|B(·)|`, `|K(·)|` at different parameters. Both assumptions are
   harmless (pad by back-and-forth moves). R4: holds throughout the paper's use.
5. **Route as a fixed sequence.** Before the meeting the agent learns nothing that depends on the other agent,
   so its route is a fixed node sequence determined by the graph, its start node and its label
   (`Explorer.route`). We do not formalize the agent as a Turing machine.
6. **Pieces, segments, atoms, borders, fences** are index intervals of the route (`iS`, `segS`, `fS`,
   `Algorithm.lean`). Segments are 0-indexed (Lean segment `i` = paper's `S_{i+1}`; Lean border `i` = paper's
   `K_{i+1,i+2}`). Pieces and fences are 1-indexed as in the paper.
7. **"Not met before".** Lemmas 3.2–3.6 assume `NoMeet E x y Ex Ey`: no meeting at a time `t` with
   `t ≤ τ_x(Ex)` and `t ≤ τ_y(Ey)`. With the indices used this is the paper's "if the agents have not met
   before / by time `t`" (in Lemma 3.6, `t` = the first time an agent completes its `(2(n+l)+1)`-th piece).
   For Lemmas 3.3–3.5 the minimal admissible indices are the end of the `(2N0)`-th fence of `x` and `y`
   (Lemma 3.5: end of piece `2N0 + 1` of `y`), so the "not met before" window of Lemma 3.5 differs slightly from its
   literal reading (until `b` ends the first atom of `S_1`); it is the window of Lemma 3.6, in which the paper
   uses these lemmas.
8. **Parameter `n + l`.** Lemmas 3.2–3.6 are proved for any `N0 ≥ n` in place of `n + l` (stronger). The
   theorem uses `N0 = n + l`, `l = 2 min(|L₁|, |L₂|) + 2`.
9. **Cost statement.** "Meeting by the time one of them performs `Π` edge traversals" is formalized as a
   meeting time `t ≤ τ_a(Π)` and `t ≤ τ_b(Π)`. Theorem 3.1's "polynomial `Π(x, y)`, non-decreasing" is
   `Π(n, m) = C (n + m + 1)^d` (`theorem_3_1`), obtained from the explicit bound `piBound P (2(n+l)+1)`
   (`theorem_3_1_explicit`) and `piBound_poly` (which needs only `P` polynomially bounded).
10. **Lemma 3.1** is formalized for an explicit interval `I = [s, e]`: `b` is inside a block `X(m, v)^c`
    of its route during `I`, and `a` follows an occurrence of `X(m, v)` within `I`. The core lemma
    `meet_of_rep` is stronger: `a` only needs to follow `R(m, v)`, the first half of `X(m, v)`.
11. **Distinct start nodes** are not needed (if they coincide, the agents meet at time 0); `theorem_3_1_ports`
    keeps the paper's assumption `va ≠ vb` only to have `n ≥ 2`.
12. **Modified labels** use the binary representation via `Nat.digits 2` (`binDigits`). The paper's "M(x) is
    never a prefix of M(y)" is used in the form `exists_bit_ne`: the two modified labels differ at a position
    `1 ≤ d < min(|M(L₁)|, |M(L₂)|)` (0-indexed; the paper's `1 < λ ≤ l`).

## Proofs: gaps and repairs

13. **Lemma 3.3 (gap, statement true; 🛠️ by R1).** The proof claims that if `a` starts no fence during `b`'s
    fence, `a` stays inside a piece. It overlooks that `a` may be inside a fence started earlier. We give a
    different argument (`lemma_3_3`). Take `j` = the last `k ≤ 2N0` such that `a` completed piece `k` by the end
    of `b`'s fence. Then:
    - `a` cannot follow a whole atom of an iteration `≥ N0` during the fence (catching against `X(2N0, v_b)`);
    - `a` cannot stay inside a piece `T_a(k)`, `k ≤ 2N0` (counting);
    - `j + 1 ≤ 2N0` in the remaining case, because `b` completed first.
14. **Length estimates in the proof of Theorem 3.1 (wrong claims inside a proof; 🛠️ by R1).**
    `|Y(k, v)| ≤ 2P(k)·Q*_k` and `|A(k, v)| ≤ 2P(k)·Z*_k` are false in general (`paper_Ystar_wrong`,
    `paper_Astar_wrong`: `10 > 6`, `42 > 12` for `P ≡ 1`; at `k = 1` the `Y` bound fails for every `P`, since
    `|Y(1)| = 4P(1)² + 6P(1) > 4P(1)² + 2P(1) = Y*_1`). With `P ≡ 1`, `n = 2`, labels `1` and `3`, the
    paper's `Π(2, 1) ≈ 2.77·10¹¹` is smaller than the position (`≈ 2.92·10¹¹`) where the longer-label agent ends
    its `(2(n+l)+1)`-th piece. So the paper's specific `Π` is not justified by its proof (computed by a script,
    not in Lean). The theorem only claims existence of a polynomial; we use exact lengths (`lenX` … `lenOm`,
    `piBound`).
15. **Lemma 3.6, Case 2, `µ = 1` (wrong reference, ⚠️-level typo inside a proof).** The contradiction comes
    from Lemma 3.3 (`a` has not completed the first atom `N` of piece `j+1` by the end of `b`'s fence), not
    from Lemma 3.4. Our proof uses Lemma 3.3's second component.
16. **Lemma 3.6's induction.** The paper argues with a minimal failing index `µ` and four cases. We prove
    Properties 1–4 by induction on `i`. Properties 1, 2 at `i` follow from Properties 3, 4 at `i - 1` (or
    Lemmas 3.5 / 3.3 for `i = 0`). Properties 3, 4 at `i` follow from Properties 1, 2 at `i`. This is the
    same argument. **Range (weaker statement):** `lemma_3_6` states the four properties only for `i` with
    `i + 1 < nSeg` for *both* agents. The paper also asserts Property 1 (resp. 2) when only the segment
    `S_i` of `a` (resp. `b`) and the border `K_{i,i+1}` of the other agent exist, i.e. for the last segment
    of the agent with the shorter modified label. This case is not formalized; its proof is the same counting
    argument, and Theorem 3.1 only uses Properties 3 and 4 below the first differing bit `λ ≤ l`.
    Lemma 3.6 also takes the conclusions of Lemmas 3.3 (second part) and 3.5 as hypotheses (for any `j`)
    instead of "`b` is first to complete its `(2(n+l))`-th fence, `j` = index of `a`"; `core` composes them.
17. **End of the proof of Theorem 3.1.** The paper's two cases per bit come from comparing when the agents
    start and finish their segments `S_λ`. We make the case analysis explicit (`meet_of_diff_bits`): from
    Properties 3 and 4 at `λ - 1`, either an atom of `a` lies within `b`'s segment or an atom of `b` lies
    within `a`'s. This is the reason for doubling the atoms. The conditions used are `n ≤ k_x ≤ 2k_y` and
    `n ≤ k_y ≤ 2k_x`.
18. **"Integral trajectory forces progress" (§3, informal; not a mistake).** "If one agent follows an integral
    trajectory during some time interval, then it must either meet the other agent or this other agent must
    perform at least one complete edge traversal during this time interval" is true if "complete" means
    "finishes a traversal" (reaches some `τ_j` in the interval). It is false if it means "performs an entire
    traversal inside the interval". Counterexample: a star with centre `w`, `b` moving from the middle of `uw`
    to the middle of `wz`, and `a` following `z, w, y, w, u` with the right timing. The counting form that the
    proofs use ("more integral trajectories than edge traversals") is correct and is `meet_of_count`, with `≥`
    instead of `>`.
19. **Lemma 2.1 (imprecisions).** `H` must reuse `G`'s port numbers on the trajectory edges. The paper does not
    say why the procedure behaves the same in `H` (same degrees and entry ports, and the exit ports used are
    occupied: `obsRun_H`). That a free port exists also needs connectivity. The port order at the new nodes
    `y_q` is arbitrary in our construction (the paper's "smallest unused port" is one choice).
20. **Small slips.** Definition 3.8's pseudocode says "Follow trajectory `Ω(k, v)`" (should be `X(k, v)`).
    Lemma 3.3's proof counts `2(2(n+l)−1)|K|` copies of `X(2(n+l))` in `Ω(2(n+l))` instead of
    `(4(n+l)−1)|K|` (harmless). §2's `|x| = ⌈log x⌉` should be `⌊log x⌋ + 1`. Lemma 3.2's "without loss of
    generality `b` is first" is unnecessary (the argument works for both orders; `lemma_3_2` is for arbitrary
    `x`, `y`).

## Not formalized

- Theorem 2.1 (procedure ESST: termination, polynomial cost, all edges traversed).
- Section 4 (Algorithm SGL and its applications: team size, leader election, perfect renaming, gossiping).
- Reingold's theorem (hypothesis, see item 3).

## Statement-level summary

All checked statements (Lemmas 2.1, 3.1–3.6, Theorem 3.1) are true as written under the paper's model with
the implicit assumptions of item 4 (R4). Proof repairs: items 13, 14. Verdict: 🛠️ Proof repaired.
