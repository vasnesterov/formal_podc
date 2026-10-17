# Differences between the formalization and the paper

Montresor, De Pellegrini, Miorandi, *Distributed k-Core Decomposition*, PODC 2011 (arXiv 1103.5320v2).
Numbering follows the arXiv version.

## False statements

1. **§4.2, worst-case family (Fig. 3): "execution time equal to N − 1 rounds for N ≥ 5" is false; it is N − 2.**
   *False statement (off by one).* In the paper's own synchronous model and with its own definition
   of execution time (number of rounds in which some node broadcasts; this accounting gives the 3
   rounds of the Fig. 2 example), the family needs exactly `N − 2` rounds for every `N ≥ 5`.
   Round 1: the degrees are broadcast, node 2 drops to 2 and the hub to 3. Rounds 2, …, N − 4:
   nodes 3, …, N − 4 drop to 2, one per round. Round N − 3: nodes N − 3 and N drop. Round N − 2:
   nodes N − 2 and N − 1 drop and broadcast; nothing changes after that. So there are N − 3
   update steps plus the initial round. The paper's
   count "N − 2 plus the last round" counts the initial broadcast round twice. Lean:
   `worstGraph_execTime` (`execTime = N − 2`), `stab_worstGraph` (`N − 3` update steps).
   The Introduction also says that §4 "describes a worst-case graph that requires exactly [N − K + 1]
   rounds". For this family `K = 1`, so `N − K + 1 = N`, while the family needs `N − 2`.
   *Not formalized, computational:* exhaustive search over all labelled graphs with `N ≤ 8` nodes shows
   that the maximum execution time is `N − 2` for `4 ≤ N ≤ 8`. So the family is optimal for these
   `N`, and the bound `N` of Theorem 5 is never attained there. The bound `N − K + 1` of Corollary 1
   is attained only when `K ≥ N − 1`.

2. **Corollary 2 (message complexity `≤ Σ_v d(v)² − 2M`) is false if the messages of the initial
   broadcast are counted.** *Imprecise statement; true for update messages.* Algorithm 1 sends
   `⟨u, d(u)⟩` to all neighbours on initialization, i.e. `2M` messages. The double-counting argument
   of §4.3 counts only updates ("each node u can at most receive d(v) − k(v) updates from each
   neighbor v"). For a single edge, `Σ d² − 2M = 0` but 2 messages are sent. Lean:
   `corollary_2_false`. We prove the bound for the update messages (rounds ≥ 2;
   `corollary_2_updates`, via the sharper per-node bound `d(u)(d(u) − k(u))`) and the bound `Σ_v d(v)²`
   for all messages (`total_messages_le`).

## Proof gaps (statements true)

3. **Theorem 5, proof.** "By definition, the execution time equals T + 1", where `T` is the first
   round with `A(T) = V`. This is off by one: with the paper's definitions the execution time equals
   `T`. Example: in Fig. 2 `T = 3` and the execution time is 3. (The paper's indexing is ambiguous:
   the Fig. 2 narrative and observation ii) "no message in rounds r + 2, …" let a node update in the
   round in which the message was sent. With that indexing `T + 1` is right, `T = 2` in Fig. 2, and the
   lost round is in observation i) instead: the nodes of minimal degree are correct before any
   message is received, i.e. in `A(0)`, not only in `A(1)`. Either way the proof loses exactly one
   round.) Because of this slip the proof first
   gets only `T ≤ N` and adds a second argument for "the tighter bound `T ≤ N − 1`". That argument is
   incomplete. It assumes that the last two wrong nodes `v₁, v₂` stay wrong together and derives a
   contradiction with liveness. The case where `v₁` becomes correct one round before `v₂` is not
   treated. Also, "core(vᵢ) = k(vᵢ) + 1" is asserted without justification. The statement is true and
   follows directly from the progress claim ("each round some node of minimal coreness among the wrong
   ones becomes correct", `progress`). With correct accounting the counting gives Corollary 1 at once:
   `execTime = stab + 1 ≤ (N − K) + 1` (`corollary_1`, `theorem_5`). The progress claim itself is argued
   only informally in the paper ("only nodes in M(r) can exchange m(r) values…"). We prove it with a
   short `(m+1)`-core argument.

4. **Theorem 3 (Liveness), induction step.** The proof builds a chain `u₁, u₂, …` of nodes of
   coreness `k` that stay above `k`, and claims that "the remaining `f − 1 ≥ k` neighbours of `u₁`
   have coreness `k + 1` or more". It then uses, for every node of the cycle, `k` neighbours of
   coreness `> k` to build a `(k+1)`-core. Neither fact follows from the assumptions: a node of
   coreness `k` may have many neighbours of coreness exactly `k`, and fewer than `k` of coreness
   `> k`. The sentence "otherwise, `u₁` would have received `f ≥ k + 1` updates equal to `k` or more,
   setting `core(u₁) = k`" is also garbled. The statement is true. We prove it with a fixpoint
   argument. The estimates are non-increasing naturals, so they stabilise. A stable vector `c` with
   `c(u) ≤ h-index of the neighbours' c` is bounded by the coreness, because `{v : c(v) ≥ c(u)}`
   induces minimum degree `≥ c(u)` (`le_coreness_of_le_hIndex`). Safety gives the other inequality.

5. **Theorem 4, proof.** "In the worst case, at most one message is broadcast per round" is
   meant as "at least one estimate decreases by at least one in every round but the first". The
   statement is proved exactly (`theorem_4`).

## Typos and small slips

6. Theorem 1, proof (⇐): "for each node v ∈ U, d_{G(U)}(v) ≥ k + 1" should be `≥ k` (the union of
   `k`-cores and `u`). "(each Wᵢ contains at least k + 1 nodes)" is irrelevant. Theorem 1 is proved
   as stated (`theorem_1`).
7. Theorem 2, proof: "|V₁| = k(u)" should be `k(u₁)`. "u₂ received a message ⟨u₂, core(u₃)⟩
   from u₃" should be `⟨u₃, core(u₃)⟩`.
8. Algorithm 2: `j ← min(k, est[v])` indexes `count[0]` when `est[v] = 0`, but `count` is indexed
   `1..k`. This never happens in an execution. `computeIndex` returns `1` (not `0`) when `k ≥ 1` and
   no neighbour has estimate `≥ 1`. So it is not literally "the largest `i` with at least `i` entries
   `≥ i`". In executions every non-isolated node's neighbours have estimate `≥ 1`, so this is
   harmless. Lean: `computeIndex` is the loop as written; `computeIndex_eq` says it returns `0` if
   `k = 0` and `max 1 (min k h)` otherwise.
9. §4.2: "the diameter is 3, i.e. a constant regardless of N". Numerically the diameter of the Fig. 3
   family is 2 for `N = 5, 6` and 3 for `N ≥ 7`. Not formalized.

## Modelling choices

10. **Graph.** A finite simple graph `G : SimpleGraph V` (`Fintype V`). Definition 1 (k-core as the
    maximum induced subgraph of minimum degree `≥ k`) is `IsKCore`. Its unique witness is `kCore`
    (`isKCore_kCore`, `IsKCore.eq_kCore`). Definition 2 is `coreness`, characterised by
    `coreness_eq_iff`. Estimates are in `ℕ∞` (`⊤` = `+∞`).
11. **Synchronous model (§4.2)** (`Run.lean`). `run G order n` is the configuration at the end of
    round `n + 1`. In each round a node processes the messages of the previous round with the handler
    of Algorithm 1 (`receive`, which calls `computeIndex` after each lowering). It does so in an
    **arbitrary order** `order` (any list of its neighbours), then broadcasts iff `changed`. Every
    result holds for every order. `run_spec` shows that the run follows the functional trajectory
    `traj` (`traj 0 = d`, `traj (s+1) u = computeIndex(traj s, u, traj s u)`), independently of the
    order. Execution time `execTime` = number of rounds in which some node broadcasts (the paper's
    definition). Round 1 always counts. For the empty graph it is `0`. `execTime_eq`:
    `execTime = stab + 1`.
12. **Asynchronous model (Theorems 2, 3 as stated for Algorithm 1)** (`Async.lean`): see that
    file's docstring. Messages may be delayed and reordered arbitrarily; ticks of the `repeat every δ`
    block are scheduled arbitrarily (a `deliver` of a message not in transit is a no-op). Liveness
    assumes fairness: every node ticks infinitely often and every message is eventually delivered
    (`Async.Fair`). The paper never states these assumptions (*under-specified*); fair schedules exist
    (`Async.exists_fair`). No FIFO assumption is needed. The paper's liveness proof also uses
    implicitly that a node's `core` is always a fixpoint of `computeIndex` on its current
    estimates (true because `computeIndex` is rerun after every lowering). Our proof uses this as an
    explicit invariant.
13. **One host, multiple nodes (§3.2, Algorithms 3–5)** (`MultiHost.lean`). The paper states no
    theorem for it ("the results can be easily extended to the one-to-many case"). We prove safety
    (`MultiHost.safety`) and liveness (`MultiHost.liveness`, `MultiHost.theorem_3_multiHost`) in
    synchronous rounds, for an arbitrary assignment `h : V → H` and arbitrary pass orders. We also
    prove that the own estimates after round `s + 1` are at most `traj s`
    (`MultiHost.ownEst_le_traj`), so the variant is never slower than the one-to-one algorithm.
    Modelling choices:
    - `improveEstimate` (Alg. 4) is defined by well-founded recursion. Its result is the greatest
      quiescent vector below the input (`improveEstimate_isGreatest`).
    - Processing all messages of a round at once and then calling `improveEstimate` equals Alg. 3's
      per-message handler for every message order (`run_succ_host_eq_receiveSeq`).
    - The sets `S` are delivered to all other hosts. This follows the text ("sent to all nodes in
      the system"); the code of Alg. 3 says `neighborH(x)`. Only entries of neighbours are ever
      read, so this does not affect the own estimates.
    - *Imprecision in the paper:* Algorithm 5 (point-to-point policy) builds `S` from all boundary
      estimates every round, without testing `changed[u]`. So it never becomes silent, which
      contradicts the "no new estimates ⇒ stop" termination criteria of §3.3. Not modelled.
14. **Not formalized.** Termination detection (§3.3), the point-to-point optimization of §3.1.2, the
    node-to-host assignment policy (§3.2.2), the remark comparing Theorems 4 and 5 (simple
    arithmetic), and the experimental section (§5).
