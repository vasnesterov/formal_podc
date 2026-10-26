# Consensus with an Abstract MAC Layer — PODC 2014

Calvin Newport. *Consensus with an abstract MAC layer.* PODC 2014. DOI
[10.1145/2611462.2611479](https://doi.org/10.1145/2611462.2611479). Formalized version: arXiv
[1405.1382](https://arxiv.org/abs/1405.1382) v1; numbering follows it.

**Verdict: ❌ False claim.** All lower bounds hold: Theorems 3.2, 3.3, 3.9 and 3.10 are proved
(Theorem 3.2 needs `n ≥ 2`). Theorem 4.1 holds for the two-phase algorithm described in the prose, with the
`2 F_ack` time bound. The pseudocode of Algorithm 1 has a one-symbol slip: line 23 looks for `decided(0)` only
in `R2`, and read literally the algorithm violates agreement on two nodes. The false statement is Claim 3.4, a numbered
claim: it fails for `D = 4` (a non-degenerate case that Theorem 3.3 covers), so the networks of Figure 1 do not
prove Theorem 3.3 there; we prove the theorem for every even `D ≥ 4` with a different gadget.

## Mistakes in the paper

* **Algorithm 1, line 23: a pseudocode slip that breaks agreement (Theorem 4.1 false if read literally).**
  Line 23 looks for `⟨phase 2, *, decided(0)⟩` in `R2` only. But a phase-2 message received during the
  receiver's own phase 1 goes into `R1` (line 6), and the loop of line 20 then does not wait for it again.
  Counterexample with two nodes, crash-free and timely (bound `F_ack = 8`):
  * `u` (input 0) gets its phase-1 ack before hearing `x` (input 1), so `u` is `decided(0)`;
  * `x`, still in phase 1, has heard `u`'s input 0 (so it will be bivalent) and receives `u`'s
    `⟨phase 2, u, decided(0)⟩` into `R1`;
  * `u` decides 0. `x` finishes phase 2 with `R2 = {⟨phase 2, x, bivalent⟩}`; both witnesses are covered by
    `R1 ∪ R2`, so it leaves the loop and decides 1.

  The intended rule is evident: line 8 already looks for phase-2 messages in `R1`, line 20 checks `R1 ∪ R2`,
  the prose says "if the set contains any message of the form decided `v_w`, then it decides `v_w`", and the
  proof assumes `v` "will see that `u` has a status of decided(0)". With the check over `R1 ∪ R2`, Theorem 4.1
  holds, including the bound "decide by `2 F_ack`". (`twoPhaseLit_not_solvesConsensus`; repaired:
  `theorem_4_1`, `theorem_4_1_time`)
* **Claim 3.4 is false for `D = 4`** (the smallest case of Theorem 3.3, not a degenerate one; theorem true). For
  `d = (D−2)/2 = 1`, node `a₂⁺` of the gadget is at distance 2 from `c`, so Network A has diameter 6, not 4
  (in Lean: the 15-node network for `k = 0`, i.e. `4 ≤ n ≤ 15`). The padding nodes `a*_j` are attached to `a_{d−1} = a₀`, which does not exist.
  Theorem 3.3 is still true for `D = 4`. We prove it for all even `D ≥ 4` with another gadget, found by computer
  search: a core `c, t, s, r, u, p`, padding twins of `p`, and a path of length `d − 1` below `t`. B is a 3-fold
  voltage cover of it. For `D ≥ 6` the paper's networks are fine (checked numerically, not formalized).
  (`claim_3_4_false_D4`; repaired: `theorem_3_3`, `exists_nets`)
* **Theorem 3.2 needs `n ≥ 2`.** With one node, deciding one's own input solves consensus with any number of
  crashes. Degenerate case. (`theorem_3_2_card_one`; `theorem_3_2` assumes `2 ≤ n`)
* **Lemma 3.1: proof gaps, statement true.**
  * Valency is defined over extensions by valid steps. Then a fragment with no deciding extension is vacuously
    both 0- and 1-valent, and it is unclear whether extensions may contain crashes.
  * Case 1 applies the valency of `β₁` to an execution in which `w` crashes. Such an execution is not an extension
    by valid steps of the paper's kind.
  * Our repair:
    * valency counts crash-free valid extensions; every reachable configuration has a possible decision;
    * the decision obtained by crashing `w` is transferred to the crash-free extension in which `w` is merely
      silent; both runs perform the same events and agree off `w`;
    * both cases of the proof become one: the two orders of the steps agree except at one node.

  (`lemma_3_1`, `exists_decision_off`, `stepV_comm`)
* **Lemma 3.8 is over-general.** It claims one `t` for lines of every length `d`. The hypothesis only concerns
  networks of diameter `D`, so only `d = D` follows, and only `d = D` is used. (`lemma_3_8`)
* **Under-specified schedulers and a w.l.o.g. step.**
  * The synchronous scheduler does not fix the order in which a node receives the messages of one round. Lemma 3.6
    needs corresponding nodes to use the same order; we sort messages by a fixed order.
  * "W.l.o.g. nodes always broadcast" is not justified. Our model allows idle nodes, so the bounds cover all
    algorithms.
* Typos: Lemma 3.8 "all nodes begin with initial value 0" should be `b`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/AbstractMAC/`, staged for CSLib as `Cslib.AbstractMAC`).
* A graph `G` and deterministic algorithms: an initial state from an identity (`Unit` = anonymous, `ℕ` = unique
  ids) and a binary input, transitions on receive and on ack, an optional broadcast, an irrevocable decision.
* Events `recv u v`, `ack u`, `crash u`; disabled events are no-ops. An ack is enabled only after every neighbour
  received the current message. Executions are sequences of blocks of events.
* Crashes. A crashed node stops and its message is no longer delivered. Deliveries *to* a crashed node are
  bookkeeping events and acks wait for them: a sub-model of the paper's, so impossibility results transfer.
* `SolvesConsensus A G id f`: agreement, validity and termination in every *timely* execution (bound `F_ack` on
  ack delay, for any `F_ack`) with diverging time and at most `f` crashes. Every fair execution is timely
  (`Fair.exists_timely`).
* Synchronous rounds, possibly holding some nodes' broadcasts for some rounds (the paper's semi-synchronous
  scheduler), with a simulation lemma for covering/embedding maps (`syncLoc_comp`) and a locality lemma
  (`syncLoc_congr_of_walk`).
* Theorem 3.2: clique, tolerance `f = 1`. All other results: no crashes (`f = 0`). Knowledge of `n` or `D` is
  modelled by quantifying only over networks with that size or diameter.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 | `lemma_3_1` | `FLP.lean` |
| bivalent initial configuration (FLP Lemma 2) | `exists_bivalent_init` | `FLP.lean` |
| Theorem 3.2 (`n ≥ 2`) | `theorem_3_2` | `FLP.lean` |
| Theorem 3.2 false for `n = 1` | `theorem_3_2_card_one` | `FLP.lean` |
| Claim 3.4 (our networks) | `exists_nets` | `Networks.lean` |
| Claim 3.4 false for `D = 4` (paper's network A) | `claim_3_4_false_D4` | `Networks.lean` |
| Lemma 3.5 | `sync_decided` | `UnknownSize.lean` |
| Lemma 3.6 + Theorem 3.3 for given networks | `not_solves_of_nets` | `Anonymous.lean` |
| Theorem 3.3 (`c = 8`) | `theorem_3_3` | `Anonymous.lean` |
| Lemma 3.8 (`d = D`) | `lemma_3_8` | `UnknownSize.lean` |
| `K_D` has diameter `D` | `kd_diam` | `UnknownSize.lean` |
| Theorem 3.9 | `theorem_3_9` | `UnknownSize.lean` |
| Theorem 3.10 | `theorem_3_10` | `TimeLB.lean` |
| Algorithm 1 with literal line 23 violates agreement | `twoPhaseLit_not_solvesConsensus` | `TwoPhase.lean` |
| Theorem 4.1 (repaired line 23) | `theorem_4_1`, `theorem_4_1_time` | `TwoPhase.lean` |

**Not formalized.** Corollary 3.7 (standard asynchronous broadcast model) and wPAXOS (Section 4.2, Lemmas 4.2–4.5,
Theorem 4.6).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity of `SolvesConsensus`: the repaired two-phase algorithm satisfies it on every clique
(`theorem_4_1`), and the trivial algorithm on one node (`theorem_3_2_card_one`). The model is new (no CSLib
abstract MAC model existed); it is staged in `Podc/Computability/Distributed/AbstractMAC/{Basic,Sync}.lean` as a
CSLib candidate.
