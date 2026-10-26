# Zigzag Causality — PODC 2017

Asa Dan, Rajit Manohar, Yoram Moses. *On Using Time Without Clocks via Zigzag Causality.* PODC 2017.
DOI [10.1145/3087801.3087839](https://doi.org/10.1145/3087801.3087839). Formalized version: arXiv
[1705.08627](https://arxiv.org/abs/1705.08627) v1 (extended version with the appendix); numbering
follows it.

**Verdict: 🚨 Headline claim false.** Theorem 4, the "Visible Zigzag Theorem" (knowledge of a timed
precedence ⇔ a σ-visible zigzag of sufficient weight), which the abstract presents as a main contribution, is false in its "only if" direction: a
4-process flooding full-information system has a node that knows `θ₁ --0--> θ₂`, but no σ-visible
zigzag from `θ₁` to `θ₂` has weight `≥ 0`. Theorem 3 also needs a hypothesis it does not state: it
fails for full-information protocols that do not flood. Theorems 1 and 2 (zigzag sufficiency and
necessity), Theorem 3 for flooding full-information protocols, and the "if" direction of Theorem 4
are proved. The "only if" direction does hold when one endpoint is a basic node of `σ`'s past.
That covers both coordination tasks (`Early`: `θ₁ = σ`; `Late`: `θ₂ = σ`), so the paper's
characterization of optimal coordination (Protocol 2) survives.

## Mistakes in the paper

* **Theorem 4 ("only if") is false.** Take processes `i, j, k, l` with channels `i→j`, `i→k`, `k→j`,
  `j→l`. All lower bounds are 1; `U_ij = U_jl = 2` and `U_ik = U_kj = 1`. Processes run a flooding
  full-information protocol (FFIP). Let `s` be an `i`-node that just received an external message,
  and set `θ₁ = ⟨s, ijl⟩`, `θ₂ = ⟨s, ikjl⟩`.
  - *`s` knows `θ₁ --0--> θ₂`.* The chain `i→k→j` reaches `j` exactly 2 units after `s`. The direct
    message `i→j` arrives after 1 or 2 units. If both arrive at `t+2` they arrive at the *same*
    `j`-node, so the two chains coincide from then on and `θ₁ = θ₂`. Otherwise `θ₁ ≤ t+3 ≤ θ₂`.
  - *No `s`-visible zigzag has weight `≥ 0`.* The past of `s` contains only `i`-nodes, since `i`
    has no incoming channel. The potential `timer(ρ) + τ(q)` on nodes `⟨ρ, q⟩`, with
    `τ(ij) = 2, τ(ik) = 1, τ(ikj) = 2, τ(ijl) = 4, τ(ikjl) = 3`, is compatible with all bounds. It
    bounds every fork and every junction of such a zigzag, so its weight is at most
    `τ(ikjl) − τ(ijl) = −1`.

  The knowledge comes from a case split over runs (merge at `j` or a gap of at least 1), and neither
  case is visible to `s`. Where the proof breaks: Lemma 18.5, case (2). In the "fast run" the chain
  of `θ₂` can merge with the chain of `θ₀ = θ₁`. The resulting time difference is the weight of a
  fork whose head is a node on `θ₁`'s chain. That node differs from `θ₂` in the actual run `r`, so
  no zigzag *in `r`* ending at `θ₂` results. The "if" direction is correct. This is a false
  statement about the paper's main structural result.

  *What we proved instead.* Necessity holds when `θ₁` or `θ₂` is a basic node in the past of `σ`
  with positive time; the other endpoint can be any σ-recognized node. That is exactly the shape
  used in Protocol 2. Our proof builds a fast run as in Definition 24 and replaces the
  longest-path lemmas 10–16 by a maximum over visible zigzags, bounded with Theorem 1.
  (`Counterexample.theorem_4_false`, `Counterexample.theorem_4_counterexample`; repaired:
  `Sys.visible_zigzag_necessity_basic`, `Sys.visible_zigzag_necessity_early`,
  `Sys.visible_zigzag_necessity_late`)
* **Theorem 3 needs flooding.** As stated it assumes nothing about the protocol. The proof uses
  Lemma 3 (needs full information), and the proof of Lemma 4 uses that a node outside the past still
  sends to every neighbour (flooding). For a full-information protocol that does not flood, Theorem 3
  is false: `D` sends to `C` and `B`; `C` replies to `B` unless it has just received `μ_go`, in which
  case it sends "go" to `A`. The delays are exact, so the reply would reach `B` together with `D`'s
  message. `B` performs `b` when it gets `D`'s message without a reply. This implements
  `Late⟨a --0--> b⟩`, but `B` learns of `μ_go` from the *absence* of a message, without a message
  chain from the go-node `σ_C`. A run in which `C` receives an extra external message together with
  `μ_go` looks the same to `B` but does not contain `σ_C`, so `K_σ(σ_C·A --0--> σ)` fails.
  We prove Theorem 3 for FFIPs, which is the setting announced in Section 2.2. Severity: a missing
  hypothesis (the paper's standing FFIP assumption covers it), not a false claim about FFIPs; the ❌
  verdict rests on Theorem 4 alone.
  (`CounterexampleFIP.theorem_3_false_for_FIP`; repaired: `Sys.thm3_late`, `Sys.thm3_early`)
* **Gaps in proofs with true statements.**
  - *Lemma 4.* The induction step treats the r-node of the sender at time `t_µ` as if it sent the
    message in `r`. That fails when the sender is still initial at `t_µ` in `r`. We fixed it with an
    extra invariant: a process activated in the constructed run was already activated in `r`.
  - *Lemma 18.* The proof assumes that the chain of `θ₀` leaves `past(r, σ)` with its first
    message, and its case analysis misses deliveries inside the past. In our repaired proof the
    zigzag starts with a fork rooted at the last past node of the chain, and from there the chain is
    delayed to its upper bounds.
  - *Lemma 12 is false as stated.* A σ-recognized node with a longer path may itself lie in the
    past, before the boundary node. The lemma is only used for nodes outside the past, where it
    holds.
  - *Theorem 4 ("if").* The proof says "`wt(Z)` depends only on the pattern". It does not:
    joinedness depends on the run. We show it is preserved for σ-visible zigzags.
* **Imprecisions.** Definition 3 says `⟨σ, p⟩` appears if `σ` appears and `p` is a path. That
  presupposes flooding and a non-initial `σ`, since initial nodes never send.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Bounded communication model without clocks, as in Section 2.
  - Time is `ℕ`. The network is a directed graph with bounds `1 ≤ L ≤ U` per channel.
  - Processes are deterministic and event-driven: they act only when something is delivered, and
    initial states never send.
  - A local state is the initial state followed by the batches received: the internal messages
    `(sender, content)` and the external messages of each activation. Time is not recorded.
  - At most one message per channel per activation.
* The environment (`Sched`) chooses the initial state in `G₀`, the delivery time of every message
  within `[L, U]`, and the external deliveries (each external message at most once). Local states
  are *computed* from these choices, so every schedule satisfying the bounds is a run of `R(P, γ)`.
* Full information means the message content determines the sender's local state. A flooding FFIP
  additionally sends to all out-neighbours at each activation. Concrete FFIPs exist; contents are
  encoded injectively into `ℕ`.
* Knowledge `K_σ φ` is truth in all runs in which the basic node `σ` appears (bridge to CSLib's
  `IndistSystem.K`: `Sys.knows_iff_K`). There are no failures and no randomness.

**Main results in Lean.** All names below are in namespace `Podc.ZigzagCausality`.

| Paper | Lean | File |
|---|---|---|
| Model, Definitions 2–4 | `Sys.st`, `Sys.Valid`, `Sys.appears`, `Sys.timer`, `Sys.recv`, `Sys.basic`, `Sys.HB` | `Model.lean`, `Basic.lean` |
| Definitions 5–7 (forks, zigzags, weight, visibility) | `Fork`, `Sys.IsZigzag`, `Sys.wtZ`, `Sys.Visible` | `Zigzag.lean` |
| Theorem 1 (zigzag sufficiency) | `Sys.zigzag_sufficiency` | `Zigzag.lean` |
| Definition 8, Lemma 1, Lemma 5 (= Lemma 2) | `Sys.BEdge`, `Sys.BPath`, `Sys.bpath_prec`, `Sys.zigzag_of_bpath` | `BoundsGraph.lean` |
| Definitions 10–11, Lemmas 8, 9 (run by timing) | `Sys.ValidTiming`, `Sys.PClosed`, `Sys.run_by_timing`, `Sys.Timing.basic_run` | `RunByTiming.lean` |
| Definitions 12–13, Lemmas 6–7, Theorem 2 (zigzag necessity) | `Sys.precSet`, `Sys.precSet_closed`, `Sys.slowTiming`, `Sys.slowTiming_valid`, `Sys.zigzag_necessity` | `Necessity.lean` |
| Lemma 3 | `Sys.HB.transfer`, `Sys.HB_iff_of_appears`, `Sys.recv_iff_of_past` | `Knowledge.lean` |
| Theorem 4, "if" | `Sys.visible_zigzag_sufficiency` | `Knowledge.lean` |
| Theorem 4, "only if" — **false** | `Counterexample.theorem_4_false` | `Counterexample.lean` |
| Definition 1, Lemma 4, Theorem 3 (for FFIP) | `CoordTask`, `Sys.ImplementsLate`, `Sys.lemma4`, `Sys.thm3_late`, `Sys.thm3_early` | `Coordination.lean` |
| Theorem 3 for non-flooding FIP — **false** | `CounterexampleFIP.theorem_3_false_for_FIP` | `CounterexampleFIP.lean` |
| Theorem 4, "only if", one endpoint basic in the past (repaired) | `Sys.visible_zigzag_necessity_basic`, `Sys.visible_zigzag_necessity_early`, `Sys.visible_zigzag_necessity_late` | `VisibleNecessity.lean` |
| Definition 24, Lemma 18 (fast run) | `Sys.FData.run`, `Sys.FData.run_valid`, `Sys.FData.timer_run` | `FastRun.lean` |
| Non-vacuity of Theorem 3 | `NonVacuity.implementsLate`, `NonVacuity.performs_exists` | `NonVacuity.lean` |

**Not formalized.** Protocols 1 and 2 (optimality claims stated informally); the "simple algorithms"
remark; footnote 3 (actions with duration).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity:
* `Counterexample.isFFIP` and `NonVacuity.isFFIP` are concrete FFIPs.
* `NonVacuity.implementsLate` and `NonVacuity.performs_exists` give an FFIP implementing
  `Late⟨a --1--> b⟩` (the fork of Figure 1) with a run in which `b` is performed, so the
  hypotheses of Theorem 3 are satisfiable.
* The counterexample runs are explicit schedules.

The model is paper-specific. Knowledge is bridged to CSLib's `Cslib.Knowledge.IndistSystem`. There
are no CSLib candidates.
