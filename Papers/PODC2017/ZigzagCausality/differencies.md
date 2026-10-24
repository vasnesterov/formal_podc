# Differences between the formalization and the paper

Paper: Dan, Manohar, Moses, *On Using Time Without Clocks via Zigzag Causality*, PODC 2017,
arXiv 1705.08627v1 (the extended version with the appendix; numbering follows it).

## Errors in the paper

1. **Theorem 4 (Visible Zigzag Theorem), "only if" direction, is false.** Counterexample in
   `Counterexample.lean` (`theorem_4_counterexample`, `theorem_4_false`): network `i → j`, `i → k`,
   `k → j`, `j → l`, all `L = 1`, `U_ij = U_jl = 2`, `U_ik = U_kj = 1`, flooding full-information
   protocol; `s` a non-initial `i`-node, `θ₁ = ⟨s, ijl⟩`, `θ₂ = ⟨s, ikjl⟩`. Then
   `K_s(θ₁ --0--> θ₂)` holds (the two chains either reach `j` at the same time — then they meet at
   the same `j`-node and `θ₁ = θ₂` — or the direct one is earlier by `≥ 1`, which compensates for
   `U_jl − L_jl = 1`), but every `s`-visible zigzag from `θ₁` to `θ₂` has weight `≤ −1`.
   The "if" direction is correct (`Knowledge.lean`). The failing step of the proof is Lemma 18.5,
   case (2): in the fast run the chain of `θ₂` may merge with the chain of `θ₀ = θ₁` (both
   delivered at the same time to the same process); the resulting time difference is the weight of
   a fork whose head is `⟨σ', p''·j·p₁'⟩`, which in `r` is a different node from `θ₂`, so no zigzag
   *in `r`* ending at `θ₂` is obtained.
2. **Repaired Theorem 4 ("only if").** We prove it when one endpoint is a basic node of the past
   of `σ` with positive time and the other is any σ-recognized node with positive time
   (`visible_zigzag_necessity_basic/early/late`, `VisibleNecessity.lean`). This covers both
   coordination tasks of Protocol 2. Proof differences: the fast run (`FastRun.lean`) uses
   closed-form times for the auxiliary nodes `ψ_k`
   (`max(1, max{T b + 1 − U(q)})`) instead of a general "valid timing of `G_E` ⇒ run" lemma (which
   the paper states without proof). The longest paths in `G_E` and Lemmas 10–16 are replaced by
   `Dz v`, the maximum weight of a σ-visible zigzag from `θ₁` to a past node `v` (bounded via
   Theorem 1). Nodes not reachable from `θ₁` are timed by their times in `r`, not by the
   `f`-longest paths of Definition 23.
3. **Gaps in the proof of Lemma 18 / Theorem 4.**
   - The proof assumes that the chain of `θ₀` leaves `past(r, σ)` at its first message. It uses
     the `E''` edge `(ψ_{i₁}, σ')`, which exists only if the message from `σ'` is not received in the
     past. Repair: start the zigzag with the fork `⟨⟨ρ,p'⟩, ⟨ρ,p'⟩, θ₁⟩`, where `⟨ρ,p'⟩` is the last
     node of the chain inside the past. From that node on, the chain is delivered at its upper
     bounds. A trivial fork prefixed at `θ₁` would not do: its head `θ₁` is not in the past.
   - The case analysis of Lemma 18.5 misses deliveries inside the past (rule 1).
   - **Lemma 12 is false as stated.** A σ-recognized `θ'` with a non-singleton path can lie in the
     past before the boundary node, and then the claimed constraint fails. It is used only for
     nodes outside the past, where it holds.

4. **Theorem 3 has no hypothesis on the protocol, but needs flooding full information.** The proof
   uses Lemma 3 (stated for an fip) and Lemma 4, whose proof uses that the r-node of a sender sends
   to every neighbour. For a full-information protocol that does not flood Theorem 3 is false
   (`CounterexampleFIP.theorem_3_false_for_FIP`: `B` infers `μ_go` from the absence of `C`'s reply;
   the same counterexample shows that Lemma 4's conclusion `σ_C ⇝ σ` is not necessary for acting —
   this last point is stated, not proved, in Lean). We prove Lemma 4 and Theorem 3 for FFIPs
   (`Sys.lemma4`, `Sys.thm3_late`, `Sys.thm3_early`), the setting announced in Section 2.2.
5. **Proof gap in Lemma 4** (statement true for FFIP): the induction step argues about the r-node
   `(j, r_j(t_µ))` of the sender as if it sent the message in `r`; this fails when `j` is still in
   its initial state at `t_µ` in `r` (initial nodes never send). Fixed with the extra invariant
   `slowRun_active` (a process activated in the constructed run at time `s` was activated in `r` by
   time `s`), which uses flooding.
6. **Theorem 4 ("if"), proof imprecision:** "since `wt(Z)` depends only on the pattern" — `S(Z)`
   (joinedness) depends on the run; for σ-visible zigzags it is preserved in every `r' ∼_σ r`
   (`Sys.adj_transfer`, `Sys.zigzag_transfer`). The hypotheses "σ-recognized" and "timer > 0" are
   not needed for this direction and are dropped.
7. **Definition 1 / "C's decision is spontaneous"** is formalized as: the go-node is the `C`-node
   whose last batch contains the external message `μ_go`, and `a` is performed at `σ_C·A`
   (`GoNode`, `CoordTask.aNode`). "Implements" asks that each `b` (a `B`-node whose state satisfies
   `doB`) is preceded/followed by `a` of some go-node by `x`; the paper's requirement that `A`
   performs `a` upon "go" is built into the definition of where `a` happens.
8. Definition 3's "appears iff σ appears and p is a path" presupposes flooding and a non-initial
   root; we use the actual message chain (`basic` is `none` if it does not exist).
9. **Theorem 2, small implicit steps** (statement and proof correct): Lemma 8 needs `V` to consist
   of nodes of `r` and uses that `T` is strictly increasing along each process inside `V` (from
   closure under predecessors); the edges of `r[T]` are stated as "edges of `G_B(r)` with target in
   `V`" (equal to the paper's induced subgraph plus isolated initial nodes); Lemma 9's second
   direction (chains in `r[T]` are chains in `r`) is proved in full; the last step uses
   `d(σ₂) ≥ 0` (empty path). The successor edges of `G_B` are between immediate successors
   (`IsSucc`: the history grows by exactly one batch).

## Modelling choices

- **Time** is `ℕ`; delays `L, U : P → P → ℕ` with `1 ≤ L ≤ U` on channels (as in the paper).
  Weights and `x` are integers.
- **Local states** are an initial state followed by the list of *batches* received at the
  activations; a batch is the `Finset` of internal messages `(sender, content)` and the `Finset`
  of external messages delivered at that time. The paper's local state is "the sequence of events
  (local actions, sends, receives)"; sends and actions are functions of the state (deterministic
  protocol), so they carry no extra information. Using a finite *set* of `(sender, content)` pairs
  means that two identical messages from the same sender delivered at the same time are seen as
  one; this cannot happen in a full-information protocol (contents determine the sender's state,
  which changes at every activation) and is irrelevant for all results.
- **Protocols** send at most one message per channel per activation (`send i ℓ j : Option M`);
  several messages on the same channel at the same time can be bundled. Processes act only when
  they receive something; an initial state never sends (as in the paper, footnote 4).
- **Runs** are generated from the environment's choices (`Sched`: initial states, delivery time of
  each message, external deliveries); `Valid` = initial state in `G₀`, every sent message delivered
  within `[L, U]`, each external message delivered at most once. This is the paper's environment
  (deliver nondeterministically in `[L, U)`, must deliver at `U`).
- **Full information** (`IsFIP`): the content of a message determines the sender's local state
  (injective encoding). FFIP (`IsFFIP`): FIP and every activated process sends to all
  out-neighbours. A concrete FFIP exists (`Counterexample.isFFIP`, contents encoded into `ℕ`).
- **General nodes** `⟨σ, p⟩` store the path *after* the root's process (`[]` = `σ` itself);
  `basic(θ, r)` is `none` when the chain does not exist in `r` (the paper's Definition 3 says
  "appears if σ appears and p is a path in Net", which presupposes flooding and a non-initial σ).
- **Zigzag patterns** are lists of forks with the conditions of Definition 6; "from θ to θ'" is
  syntactic equality of the first tail / last head, as in the paper. "Joined" means the head and
  the next tail are the same *basic* node in `r`.
- **Knowledge** `Knows σ φ`: `φ` holds in every valid run in which `σ` appears (the paper's
  `r ∼_σ r'`).
