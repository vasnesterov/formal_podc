# Differences between the formalization and the paper

Paper: Alistarh, Gelashvili, Vojnović, *Fast and Exact Majority in Population Protocols*, PODC 2015,
full version MSR-TR-2015-13.

## Statement-level issues

1. **Figure 1, line 12 (✏️ slip).** Printed: `weight(x) · weight(y) = 0 and value(x) + value(y) > 0`.
   Read literally, a weak state meeting a state of negative value is left unchanged (line 19), so `+0`
   never turns into `−0`. AVC then fails to compute the majority when `B` is the majority:
   `literal_fails` (`m = d = 1`, inputs `A, B, B`: one interaction gives the silent configuration
   `−0, +0, −1₁`) and `not_tendsto_literal` (under the uniform random scheduler the probability of
   not having converged stays bounded away from `0`). The script `tools/avc.py` shows failures for
   every tested parameter set (`n ≤ 5`, `m ≤ 5`, `d ≤ 2`), e.g. inputs `A, B, B` with `m = 3`.
   The intended condition is recoverable from the
   paper ("if a node with 0 weight meets a node with non-zero weight, then it will adopt the sign of
   the interaction partner", Section 3), the fix is local (`value` → `weight`), and the proof of Lemma
   A.1 never uses the printed condition: it argues "w.l.o.g. `S > 0`" with the prose semantics. We
   formalize the corrected protocol (`avc`, `update false`) and prove it correct. The corrected
   protocol is exactly sign-symmetric (`update_neg`), which justifies the paper's w.l.o.g.
   The published pseudocode of the main algorithm is wrong for half of the inputs; we treat it as a
   typo because of the explicit prose description.

No other statement was found false. Theorem B.1 is not refuted, but see item 7.

## Modelling choices

2. **AVC states.** `St.zero pos` (`±0`), `St.one pos j` (`±1_j`), `St.strong v` (value `v`). The
   transition function does not depend on `m`; `m` only enters through `St.Valid m d` (odd
   `3 ≤ |v| ≤ m`, `1 ≤ j ≤ d`), which is closed (`valid_update`, requires `m` odd and `d ≥ 1`, as in
   the paper). `R↓/R↑` and `ϕ` are as in Figure 1. The initial states are `ϕ(±m)`, i.e. `±1₁` when
   `m = 1` (the paper: "nodes start in states +1 or −1").
3. **Probability 1.** Lemma A.1 and Theorem 4.1 say "with probability 1". We prove that the
   probability of not being converged after `t` steps tends to `0` (`lemma_A_1`,
   `theorem_4_1_correct`), and separately that converged configurations are closed
   (`converged_closed`, `lemma_A_1_closed`). Together they give "w.p. 1 the execution reaches a
   configuration after which all outputs are correct forever". The probabilistic statements live on
   the finite type of valid states `VSt m d`.
4. **Lemma A.1, scope.** The lemma holds for *every* valid configuration with `S ≠ 0`, not only
   initial ones, as in the paper. Its expected-time bound `n³(m + d + 1)` is not formalized.
5. **Section 2's definition of "solves majority within `ℓ` steps with probability `1 − φ`"** is not
   formalized; Theorem 4.1's correctness part is the limit statement above.
6. **Theorem B.1, configurations.** The three correctness properties are stated on anonymous
   configurations (multisets of states, `Four.Correct`), for every population size; steps fire
   `P.δ p q` on two agents in states `p, q` in either role. This is the projection of the labelled
   model to counts and equivalent to it because protocols cannot see identities; the bridge
   labelled ↔ multiset is not formalized. The lower bound (`theorem_B_1`) is stated for CSLib's
   labelled uniform scheduler, so the two parts meet through `Invariant P`, a property of `δ` only.
7. **⚠️ Theorem B.1, unordered interactions (hypothesis `Symmetric P`).** Section 2 defines ordered
   `δ`; Appendix B says "interacting nodes are not ordered (`[S0, X]` is the same as `[X, S0]`)" and
   its whole case analysis assigns one outcome per unordered pair. We add this as the hypothesis
   `Symmetric P` (both orientations produce the same multiset). Claims B.2–B.5 are proved without
   it, for both orientations. For ordered protocols the remaining case analysis is only
   model-checked (`tools/genasym.py`, populations ≤ 5, both values of `γ(X)`). The search tree has
   about 1.2 million leaves per case, every non-invariant ordered protocol is refuted, and 2490
   leaves are invariant. That is evidence that the theorem holds for ordered protocols too, but the
   paper's proof does not cover them. This is a proof gap of the paper: the statement is not
   refuted. The restriction is not an implied assumption: Section 2 fixes ordered `δ`, and AVC
   itself distinguishes initiator and responder. In Lean the ordered case stays
   unestablished; `Symmetric P` is a multiset condition, so protocols whose two orientations differ
   only in which agent gets which state are covered.
8. **The output set.** `γ : Q4 → Bool` (`false` = 0, `true` = 1). The paper's "w.l.o.g. `γ` assigns 0
   or 1 to each state" is built in.
9. **Property 1** (`C_i` non-empty) is part of `Correct` but not needed by the proof (neither the
   paper's nor ours).

## Proof-level differences

10. **Case analysis of Theorem B.1.** We do not formalize Claims B.6, B.7, B.9 and Cases 1–3
    one by one. Their combined consequence, every correct symmetric protocol preserves
    `#S0 − #S1`, is proved by two kernel-checked certified case trees (`treeA`, `treeB`,
    `checkTree_sound`) that split on the outcomes of the four "cross" pairs. Each leaf certificate
    uses at most 7 agents (at most 5 in `treeB`): a Claim B.2 collision, a reachable closed set violating the second
    property, or a reachable closed set violating the third property (the paper's potential
    arguments of Claim B.9 are instances of the last kind). We replayed the explicit interaction
    sequences of Claims B.6, B.7 and Cases 1.1–2.4 by script; they are correct up to the slips listed
    in item 13.
11. **Claim B.4 / B.5** are formalized as in the paper (`n = 9`, `n = 5`, `n = 7`; pigeonhole).
    Claim B.5 is stated as "same-output pairs keep or swap their states", for both orientations, and
    its first step (outcomes stay in `{S_i, x_i}`) uses the mixed absorbing configuration of Claim
    B.4, as in the paper.
12. **Claim B.8 / the `Ω(1/ϵ)` bound (🔧 for the meeting probability).**
    - The probability that the unique minority agent meets one of the `ϵn + 1` majority agents is
      `2(ϵn + 1)/(n(n − 1))` under the uniform ordered-pair scheduler; the paper writes
      `(ϵn + 1)/n²` (factor ≈ 2; harmless for `Ω`). Claim B.8 sits inside the proof of Theorem
      B.1 and its conclusion is true.
    - Only majority `S0` is stated (`theorem_B_1`); majority `S1` is the same after exchanging
      `S0 ↔ S1` and `X ↔ Y`.
    - We prove the tail bound `P(τ ≤ t) ≤ t · 2(D+1)/(n(n−1))` (`hitProb_le`; `D = #S0 − #S1 ≥ 0`
      is preserved, at least one `S1` initially), where `τ` is the first time without agents in `S1`.
      Configurations of `C_0` have no `S1` (since `γ(S1) = 1`), so `theorem_B_1` bounds the
      probability of reaching any all-output-0 configuration. Instead of the expectation over the
      path space we prove `∑_{t<K} P(τ > t) ≥ K − p·K(K−1)/2` (`sum_tail_ge`), a lower bound for
      `E[τ] = ∑_t P(τ > t)`. Taking `K ≈ 1/p` gives `E[τ] ≳ n(n−1)/(4(ϵn+1))` steps, i.e.
      `Ω(1/ϵ)` parallel time. The paper counts "clutch rounds" (a geometric number), which gives the
      same order.
    - `P(τ ≤ t)` is defined by the first-step recursion `hitProb` (probability of visiting a set
      within `t` steps), not via a measure on executions.
13. **Typos in Appendix B** (no effect): "two nodes in S9" (Case 1) means `S0`; "three nodes
    starting in C0" (Case 2.3) means `S0`; in Case 2.4.1 "this interaction from I would lead to a
    configuration with two nodes in X and three nodes in S1" needs two applications of
    `[X, Y] → [S1, X]`; in Case 2.4.1 ("`[X, Y]` into `[S0, Y]`") the contradiction is with the second
    property (an absorbing configuration of `C_0` reached from majority `S1`), not the third.
14. **Lemma A.1 proof.** Formalized along the paper's three phases, as a reachability argument
    (`phase1`, `phase2`, `phase3`) with the measures "total negative weight", "number of negative
    agents" and "number of `−0` agents". Phase 1 picks a strong node and a node of opposite sign and
    non-zero value, as in the paper; phase 2 lets one fixed pair `−1_i`, `+1_j` interact until both
    are weak (at most `d` interactions). The w.l.o.g. `S > 0` is justified by `update_neg` /
    `reachable_neg` (sign symmetry of the corrected protocol).

## Not formalized

- Theorem 4.1's convergence-time bounds and Corollary 4.2 (Claims A.2, A.3, A.4, 4.4, 4.5;
  Chernoff-type concentration).
- The expected-time bound of Lemma A.1.
- Theorem C.1 (`Ω(log n)` for any number of states).
- Theorem B.1 for ordered (asymmetric) four-state protocols (only model-checked, item 7).
