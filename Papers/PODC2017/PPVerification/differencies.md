# Differences between the formalization and the paper

Paper: Blondin, Esparza, Jaax, Meyer, *Towards Efficient Verification of Population Protocols*, PODC 2017
(arXiv 1703.04367v3).

## Model and definitions

1. **Configurations.** The paper uses `Pop(Q)`, multisets with at least 2 agents. We use all of
   `Multiset Q`. The bound `|C| ≥ 2` is kept for inputs (`MProtocol.IsInitial`, `WellSpecified`:
   `2 ≤ card X`). In Termination, Silence and Definition 4, configurations with fewer than 2 agents are
   terminal and start no execution, so the definitions are equivalent.
2. **Transitions** are a `Set (Transition Q)` of quadruples `(p, q, p', q')`, with totality as a field of
   `MProtocol`. `Transition.Silent` is `pre = post`, as in the paper. `P[S]` (`MProtocol.restrict`) adds the
   identity transitions `(p, q, p, q)`.
3. **Executions and fairness.** An execution is a CSLib `TransitionSystem.Run` of the step relation.
   Fairness is the paper's edge fairness (`Run.EdgeFair`). "Silent execution" is `Run.Silent`
   (eventually constant).
4. **Ordered partitions** are lists `[T₁, …, Tₙ]` (`IsOrderedPartition`: nonempty parts, pairwise
   disjoint, union `T`). `T₁ ∪ ⋯ ∪ Tᵢ₋₁` is `layersBelow L i`.
5. **Potential reachability** (Def. 12). `x : Transition Q → ℕ` must be supported on `T`. The flow
   equations are over `ℤ`. Traps and siphons are `Finset`s of states. "`U`-trap" is `IsUTrap U R`
   (`R• ∩ U ⊆ •R`), "`U`-siphon" is `IsUSiphon U R`. The constraints are stated, as in Def. 12, for `U = ⟦x⟧`.
6. **Termination, Consensus, StrongConsensus** are transcribed literally. The consensus output is
   `IsConsensus O C b` (`∀ q ∈ C, O q = b`).

## Statements

7. **Proposition 19** is proved as the paper's stronger form. (a) is `MProtocol.silent_iff_termination`,
   (b) is `MProtocol.wellSpecified_iff_consensus`. The paper's "(a ⇒) follows immediately" needs the
   existence of fair executions. For edge fairness this is `exists_edgeFair`: CSLib's round-robin globally
   fair run, applied to the system whose states are the transitions.
8. **Proposition 20**: as stated.
9. **StrongConsensus ⇒ Consensus, WS³ ⊆ WS² ⊆ WS**: as stated (§4.3). Observation 11 is proved for firing
   sequences (`FiresSeq.trap`, `FiresSeq.siphon`).
10. **Lemma 21.** The paper's statement indexes `x` by states ("`x(q) ≥ 0` for every `q ∈ Q`,
    `x(q) > 0` for some `q`"); it must be by transitions. We take `x : Transition Q → ℚ` with support in the
    non-silent transitions of `T`, `x ≥ 0`, `x ≠ 0`, and `∑ₜ x(t) · (post(t)(q) − pre(t)(q)) = 0` for all `q`.
    `lemma_21_set` holds for any set of transitions (no totality needed); `lemma_21` is the protocol version.
11. **Lemma 22** is stated for arbitrary sets `S` (the steps) and `U` (the dead transitions) as
    `¬ PreservesDead S U ↔ ∃ s ∈ S, ∃ u ∈ U non-silent, ∀ non-silent u' ∈ U, pre(u') ≰ pre(s) + (pre(u) ⊖ post(s))`.
    The paper fixes `S = T \ U`, but Prop. 7 applies it to `P[Tᵢ]`. The polynomial-time claim is not
    formalized.
12. **`P_thr`.**
    * The paper says `T` *contains* the transitions of leader initiators and does not specify the other pairs,
      although the model requires totality. We add the identity transitions for pairs whose first state is a
      non-leader (as in Example 1). They are silent, so reachability, potential reachability, terminal
      configurations and (up to stuttering) fair executions are unchanged.
    * We prove everything for any bound `v ≥ |c| + 1` with all `|aᵢ| ≤ v` (`Threshold.protocol`). The paper's
      `vmax = max(|a₁|, …, |a_k|, |c| + 1)` is `Threshold.Pthr` (`Finset.fold max`).
    * The input alphabet is any type `Λ` (a `Fintype` for `vmax`), not `{x₁, …, x_k}` with `k ≥ 1`.
    * Leader, opinion are `Bool`s; values are `Set.Icc (-v) v`.
13. **Proposition 23**: as stated (`flowEq_val`), for `x` supported on the transitions of `P_thr`.
14. **Proposition 24** is proved in the stronger form `consensus_of_terminal`: a terminal configuration with
    a leader and at least 2 agents is a consensus whose output is `val(C) < c`. The paper's two claims
    follow. The proof uses a second agent (to force the leader's opinion to match its value); in the paper this
    is `|C| ≥ 2` from `C ∈ Pop(Q)`. Since our configurations are arbitrary multisets, we add `2 ≤ card C` as a
    hypothesis and discharge it in Prop. 17 by `FlowEq.card_eq` (the flow equations preserve the population size).
15. **Proposition 17**: as stated (`proposition_17`, and `proposition_17_Pthr` for `vmax`). The explicit
    output `val(I(X)) < c` is `consensus_of_potReach`. In the trap argument for "`C'` contains a leader", the
    case where no transition of `⟦x⟧` moves an agent into the leaders is handled by the flow equations
    (`exists_leader_of_potReachVia`). The paper does not cover this case; for its literal `P_thr` (every listed
    transition moves an agent into the leaders) it is only `x = 0`, for ours also `x` supported on the added
    silent non-leader transitions.
16. **Proposition 18.**
    * The paper gives the partition `T₁ = {t : pre(t) ≠ ⦃q, r⦄, q ∈ L₀, r ∈ N₁}`, `T₂ = T \ T₁` for
      `c > 0`, and a symmetric one for `c ≤ 0`. We prove that the first partition works for **every** `c`
      (`proposition_18_with`).
    * Bounded model checking (`v ≤ 3`, up to 3 agents) indicates that the `c ≤ 0` partition also works for every `c`.
      It is not formalized.
    * Silence of `P_thr[T₁]` uses a new proof: a lexicographic ranking (number of leaders, `∑` |values| of
      non-leaders, number of leaders with inconsistent opinion, number of "flippable" non-leaders). The paper's
      argument has a false step (`a₀ ≥ a₁ ≥ ⋯`, refuted by `nonleaderAbs_not_antitone`) and misses the saturated
      transitions (`saturated_flip`).
    * Silence of `P_thr[T₂]` (`t2_silent`) and `T₁`-deadness of `P_thr[T₂]` (`t2_dead`) follow the paper.
17. **Bonus**: `pthr_ws3` (`P_thr ∈ WS³`) and `pthr_computes`: every fair execution of `P_thr` from `I(X)`
    stabilizes to `∑ a(i) X(i) < c`, i.e. `P_thr` computes the threshold predicate. The paper only claims
    membership in WS³.

## Not formalized

18. The complexity results: Prop. 3 (EXPSPACE-hardness), Props. 6, 7 (polynomial-time checks), Cor. 8,
    Prop. 15 (coNP), Thm. 16 (DP). The polynomial-time claims of Lemma 22 and the maximal trap/siphon remark of §4.2.
19. The remainder protocol (Props. 25, 26), closure under negation and conjunction (Props. 27–29), and hence
    "WS³ is as expressive as WS". The experiments (§6).

## Typos (no formal consequence)

20. Proof of Prop. 18: "every execution of `P_thr[T₁]` is fair" means "silent". "such transitions set the
    opinion of non leaders to 0" should be "to 1".
21. Observation 11: "if `C(S) = 0`" should read "`C(P) = 0`".
